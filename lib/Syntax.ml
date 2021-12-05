module StringSet = Set.Make(String)

type expr_t =
  | EUnit
  | EVar of string
  | EAbs of string * expr_t
  | EApp of expr_t * expr_t
  | EAnn of expr_t * type_t

and type_t =
  | TUnit : type_t
  | TVar : string -> type_t
  | TExists : string -> type_t
  | TForall : string * type_t -> type_t
  | TFun : type_t * type_t -> type_t

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

let rec is_monotype = function
  | TUnit -> true
  | TVar _ -> true
  | TExists _ -> true
  | TForall _ -> false
  | TFun (u, v) -> is_monotype u && is_monotype v

let rec free_type_vars = function
  | TUnit -> StringSet.empty
  | TVar v -> StringSet.singleton v
  | TExists v -> StringSet.singleton v
  | TForall (v, t) -> StringSet.remove v (free_type_vars t)
  | TFun (u, v) -> StringSet.union (free_type_vars u) (free_type_vars v)
