open Syntax

type complete
type incomplete

type 'a element =
  | CVar : string * Syntax.poly Syntax.type_t -> 'a element
  | CForall : string -> 'a element
  | CExists : string -> incomplete element
  | CSolved : string * Syntax.mono Syntax.type_t -> 'a element
  | CMarker : string -> 'a element

type 'a t = 'a element list

type error = [ | `CouldNotDropMarker ]

let empty : type a. a t = []

let (|>) (type a) (es : a t) (e : a element) : a t = e :: es

let rec apply_context : type a b. a t -> b Syntax.type_t -> Syntax.poly Syntax.type_t =
  function gamma ->
    function
    | TUnit -> TUnit
    | TVar n -> TVar n
    | TExists n ->
       let findSolved : a element -> Syntax.poly Syntax.type_t option = function
         | (CSolved (m, t)) when n == m -> Some (Syntax.polytype t)
         | _ -> None

       in (match List.find_map findSolved gamma with
           | Some solved -> apply_context gamma solved
           | None -> TExists n)
    | TForall (n, t) -> TForall (n, apply_context gamma t)
    | TFun (a, b) -> TFun (apply_context gamma a, apply_context gamma b)

module Query = struct
   let collect (type a) (predicate : string list -> a element -> string list) : a t -> string list =
     List.fold_left predicate []

   let vars (type a) (xs : string list) : a element -> string list =
     function
     | CVar (x, _) -> x :: xs
     | _ -> xs

   let foralls (type a) (xs : string list) : a element -> string list =
     function
     | CForall x -> x :: xs
     | _ -> xs

   let existentials (type a) (xs : string list) : a element -> string list =
     function
     | CExists x -> x :: xs
     | CSolved (x, _) -> x :: xs
     | _ -> xs

   let markers (type a) (xs : string list) : a element -> string list =
     function
     | CMarker x -> x :: xs
     | _ -> xs
end

module Alter = struct
  let pop_until (type a) (e : a element) =
    let rec aux = function
      | [] -> None
      | x :: xs -> if (x = e) then Some xs else aux xs in
    aux

  let break_at (type a) (e : a element) =
    let rec aux ys = function
      | [] -> None
      | x :: xs -> if (x = e) then Some (List.rev ys, xs) else aux (x :: ys) xs in
    aux []

  let drop_marker (type a) (m : a element) (c : a t) : (a t, [> error]) result =
    match Base.List.tl (Base.List.drop_while c ~f:(function n -> n != m)) with
    | Some c' -> Ok c'
    | None -> Error `CouldNotDropMarker
end
