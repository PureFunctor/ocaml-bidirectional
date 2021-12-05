module StringSet = Set.Make(String)

module Syntax = struct
  (* Variants of expressions. *)
  type expr_t =
    | EUnit
    | EVar of string
    | EAbs of string * expr_t
    | EApp of expr_t * expr_t
    | EAnn of expr_t * type_t

  (* Variants of types. *)
  and type_t =
    | TUnit : type_t
    | TVar : string -> type_t
    | TExists : string -> type_t
    | TForall : string * type_t -> type_t
    | TFun : type_t * type_t -> type_t

  (* [expr_subst e n] substitutes all occurences of n with e. *)
  let rec expr_subst (e : expr_t) (n : string) = function
    | EUnit ->
       EUnit
    | EVar v ->
       if n = v then e else EVar v
    (* An abstraction must be renamed with respect to the variables that
       it binds. If we get name collisions with a newly introduced name,
       then we avoid substituting further. *)
    | EAbs (v, b) ->
       if n = v then EAbs (v, b) else EAbs (v, expr_subst e n b)
    | EApp (f, x) ->
       EApp (expr_subst e n f, expr_subst e n x)
    | EAnn (v, t) ->
       EAnn (expr_subst e n v, t)

  (* [type_subst e n] substitutes all occurences of n with t. *)
  let rec type_subst (t : type_t) (n : string) = function
    | TUnit ->
       TUnit
    | TVar v ->
       if n = v then t else TVar v
    | TExists v ->
       if n = v then t else TExists v
    (* An abstraction must be renamed with respect to the variables that
       it binds. If we get name collisions with a newly introduced name,
       then we avoid substituting further. *)
    | TForall (v, u) ->
       if n = v then TForall (v, u) else TForall (v, type_subst t n u)
    | TFun (u, v) ->
       TFun (type_subst t n u, type_subst t n v)

  (* [monotype t] determines whether a type t is a monotype at runtime. *)
  let rec (monotype : type_t -> type_t option) = function
    | TUnit -> Some TUnit
    | TVar v -> Some (TVar v)
    | TExists v -> Some (TExists v)
    | TForall _ -> None
    | TFun (u, v) ->
       match (monotype u, monotype v) with
       | (Some u', Some v') -> Some (TFun (u', v'))
       | _ -> None

  (* [polytype t] determines whether a type t is a polytype at runtime. *)
  let rec (polytype : type_t -> type_t) = function
    | TUnit -> TUnit
    | TVar v -> TVar v
    | TExists v -> TExists v
    | TForall (v, t) -> TForall (v, t)
    | TFun (u, v) -> TFun (polytype u, polytype v)

  (* [free_type_vars t] collects the free type variables in some type t. *)
  let rec free_type_vars = function
    | TUnit -> StringSet.empty
    | TVar v -> StringSet.singleton v
    | TExists v -> StringSet.singleton v
    | TForall (v, t) -> StringSet.remove v (free_type_vars t)
    | TFun (u, v) -> StringSet.union (free_type_vars u) (free_type_vars v)
end

module Context = struct
  (* Variants of context elements *)
  type element =
    | CVar : string * Syntax.type_t -> element
    | CForall : string -> element
    | CExists : string -> element
    | CSolved : string * Syntax.type_t -> element
    | CMarker : string -> element

  (* A context is simply a reversed linked list *)
  type t = element list

  (* [empty] is a context with no elements *)
  let (empty : t) = []

  (* [(|>)] appends an element to the tail of the context *)
  let (|>) (es : t) (e : element) : t = e :: es

  (* [popUntil e es] pops items from the context until before e  *)
  let popUntil (e : element) =
    let rec aux = function
      | [] -> None
      | x :: xs -> if (x = e) then Some xs else aux xs in
    aux

  (* [breakAt e es] breaks apart a context at some element e *)
  let breakAt (e : element) =
    let rec aux ys = function
      | [] -> None
      | x :: xs -> if (x = e) then Some (List.rev ys, xs) else aux (x :: ys) xs in
    aux []

  (* [collect predicate] collects type variables from the context given
     a predicate. *)
  let collect (predicate : string list -> element -> string list) : t -> string list =
    List.fold_left predicate []
end

module WellFormed = struct
  let rec well_formed_type (context : Context.t) : Syntax.type_t -> bool = function
    | TUnit -> true
    | TVar v ->
       let predicate xs = function
         | Context.CForall x -> x :: xs
         | _ -> xs in
       List.mem v (Context.collect predicate context)
    | TExists v ->
       let predicate xs = function
         | Context.CExists x -> x :: xs
         | _ -> xs in
       List.mem v (Context.collect predicate context)
    | TForall (v, t) ->
       well_formed_type Context.(context |> CForall v) t
    | TFun (u, v) ->
       well_formed_type context u && well_formed_type context v

  let rec well_formed_context = function
    | [] -> true
    | e :: es ->
       let head =
         match e with
         | Context.CVar (v, t) ->
            let predicate xs = function
              | Context.CVar (x, _) -> x :: xs
              | _ -> xs in
            not (List.mem v (Context.collect predicate es)) && well_formed_type es t

         | Context.CForall v ->
            let predicate xs = function
              | Context.CForall x -> x :: xs
              | _ -> xs in
            not (List.mem v (Context.collect predicate es))

         | Context.CExists v ->
            let predicate xs = function
              | Context.CExists x -> x :: xs
              | Context.CSolved (x, _) -> x :: xs
              | _ -> xs in
            not (List.mem v (Context.collect predicate es))

         | Context.CSolved (v, t) ->
            let predicate xs = function
              | Context.CExists x -> x :: xs
              | Context.CSolved (x, _) -> x :: xs
              | _ -> xs in
            not (List.mem v (Context.collect predicate es)) && well_formed_type es t

         | Context.CMarker v ->
            let predicate xs = function
              | Context.CMarker x -> x :: xs
              | _ -> xs in
            not (List.mem v (Context.collect predicate es))

       in head && well_formed_context es

end

class fresh = object
  val mutable index = 0

  method fresh =
    let prefix = String.make 1 (Char.chr (97 + index / 26)) in
    let suffix = string_of_int (index mod 26) in
    index <- index + 1;
    String.cat prefix suffix

  method reset =
    index <- 0
end
