open Syntax

type complete
type incomplete

type 'a element =
  | CVar : string * polytype_t -> 'a element
  | CForall : string -> 'a element
  | CExists : string -> incomplete element
  | CSolved : string * monotype_t -> 'a element
  | CMarker : string -> 'a element

type 'a t = 'a element list

type complete_t = complete t

type incomplete_t = incomplete t

type error = [ | `CouldNotDropMarker | `CouldNotBreakContext | `NotWellFormed ]

let empty : type a. a t = []

let (|>) (type a) (es : a t) (e : a element) : a t = e :: es

let rec apply_context : type a b. a t -> b Syntax.type_t -> Syntax.poly Syntax.type_t =
  function gamma ->
    function
    | TUnit -> TUnit
    | TVar n -> TVar n
    | TExists n ->
       let findSolved : a element -> Syntax.poly Syntax.type_t option = function
         | (CSolved (m, t)) when n = m -> Some (Syntax.polytype t)
         | _ -> None

       in (match List.find_map findSolved gamma with
           | Some solved -> apply_context gamma solved
           | None -> TExists n)
    | TForall (n, t) -> TForall (n, apply_context gamma t)
    | TFun (a, b) -> TFun (apply_context gamma a, apply_context gamma b)

let collect (type a) (predicate : string list -> a element -> string list) : a t -> string list =
  List.fold_left predicate []

let collect_vars (type a) : a t -> _ = fun context ->
  let predicate xs : _ element -> _ =
    function
    | CVar (x, _) -> x :: xs
    | _ -> xs
  in collect predicate context

let collect_foralls (type a) : a t -> string list = fun context ->
  let predicate xs : a element -> _ =
    function
    | CForall x -> x :: xs
    | _ -> xs
  in collect predicate context

let collect_existentials (type a) : a t -> string list = fun context ->
  let predicate xs : a element -> _ =
    function
    | CExists x -> x :: xs
    | CSolved (x, _) -> x :: xs
    | _ -> xs
  in collect predicate context

let collect_unsolved (type a) : a t -> string list = fun context ->
  let predicate xs : a element -> _ =
    function
    | CExists x -> x :: xs
    | _ -> xs
  in collect predicate context

let collect_markers (type a) : a t -> string list = fun context ->
  let predicate xs : a element -> _ =
    function
    | CMarker x -> x :: xs
    | _ -> xs
  in collect predicate context

let pop_until (type a) (e : a element) =
  let rec aux = function
    | [] -> None
    | x :: xs -> if (x = e) then Some xs else aux xs in
  aux

let break_at (type a) (e : a element) =
  let rec aux ys = function
    | [] -> Error `CouldNotBreakContext
    | x :: xs -> if (x = e) then Ok (List.rev ys, xs) else aux (x :: ys) xs in
  aux []

let (let*) = Result.bind

let insert_at (type a) : a t -> a element -> a t -> (a t, [> error]) result = fun gamma m theta ->
  let* (gammaL, gammaR) = break_at m gamma in
  Ok (List.append (List.append gammaL theta) gammaR)

let drop_marker (type a) (m : a element) (c : a t) : (a t, [> error]) result =
  match Base.List.tl (Base.List.drop_while c ~f:(function n -> n <> m)) with
  | Some c' -> Ok c'
  | None -> Error `CouldNotDropMarker

module WellFormed = struct
  let rec check_type : type a b. a t -> b type_t -> (unit, [> error]) result = fun context ->
    function
    | TUnit ->
       Ok ()
    | TVar v ->
       if List.mem v (collect_foralls context) then
         Ok ()
       else
         Error `NotWellFormed
    | TExists v ->
       if List.mem v (collect_existentials context) then
         Ok ()
       else
         Error `NotWellFormed
    | TForall (v, t) ->
       check_type (context |> CForall v) t
    | TFun (u, v) ->
       match check_type context u, check_type context v with
       | Ok _, Ok _ -> Ok ()
       | _ -> Error `NotWellFormed

  let check_context =
    function context ->
      let rec aux continue = function
        | _ when not continue -> false
        | [] -> true
        | e :: es ->
           let no_duplicates name collect =
             not (List.mem name (collect es)) in
           let continue' = match e with
             | CVar (n, t) ->
                no_duplicates n collect_vars && Result.is_ok (check_type es t)

             | CForall n ->
                no_duplicates n collect_foralls

             | CExists n ->
                no_duplicates n collect_existentials

             | CSolved (n, t) ->
                no_duplicates n collect_existentials && Result.is_ok (check_type es t)

         | CMarker n ->
            no_duplicates n collect_markers
           in aux continue' es
      in if aux true context then
           Ok ()
         else
           Error `NotWellFormed
end

let solve_context (gamma : incomplete_t) (alpha : string) (tau : monotype_t) : (incomplete_t, [> error]) result =
  let* (gammaL, gammaR) = break_at (CExists alpha) gamma in
  let* _ = WellFormed.check_type gammaR tau in
  let gammaR' = gammaR |> CSolved (alpha, tau) in
  Ok (List.append gammaL gammaR')

let ordered_context (gamma : incomplete_t) (alpha : string) (beta : string) =
  match drop_marker (CExists beta) gamma with
  | Ok gammaL -> List.mem alpha (collect_existentials gammaL)
  | Error _ -> false
