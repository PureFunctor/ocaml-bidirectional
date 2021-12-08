open Context
open Syntax

let rec check_type : type a b. a Context.t -> b type_t -> bool = fun context ->
  function
  | TUnit ->
     true
  | TVar v ->
     let predicate xs = function
       | CForall x -> x :: xs
       | _ -> xs in
     List.mem v (Context.collect predicate context)
  | TExists v ->
     let predicate (xs : string list) : a Context.element -> string list = function
       | CExists x -> x :: xs
       | CSolved (x, _) -> x :: xs
       | _ -> xs in
     List.mem v (Context.collect predicate context)
  | TForall (v, t) ->
     check_type (context |> CForall v) t
  | TFun (u, v) ->
     check_type context u && check_type context v

let check_context : type a. a Context.t -> bool = function context ->
  let rec aux (continue : bool) : a Context.t -> bool = function
    | _ when not continue -> false
    | [] -> true
    | e :: es ->
       let no_duplicates name predicate =
         not (List.mem name (Context.collect predicate es)) in
       let continue' = match e with
         | CVar (n, t) ->
            no_duplicates n context_vars && check_type es t

         | CForall n ->
            no_duplicates n context_foralls

         | CExists n ->
            no_duplicates n context_existentials

         | CSolved (n, t) ->
            no_duplicates n context_existentials && check_type es t

         | CMarker n ->
            no_duplicates n context_markers
       in aux continue' es
  in aux true context