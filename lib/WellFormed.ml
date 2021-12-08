open Context
open Syntax

type error = [ | `NotWellFormed ]

let (let*) = Result.bind

let rec check_type : type a b. a Context.t -> b type_t -> (unit, [> error]) result = fun context ->
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

let check_context : type a. a Context.t -> (unit, [> error]) result = function context ->
  let rec aux (continue : bool) : a Context.t -> bool = function
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
