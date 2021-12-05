module StringSet = Set.Make(String)

module Syntax = struct
  (* Type-only markers for GADTs *)
  type mono
  type poly

  (* Variants of expressions. *)
  type expr_t =
    | EUnit
    | EVar of string
    | EAbs of string * expr_t
    | EApp of expr_t * expr_t
    | EAnn of expr_t * poly type_t

  (* Variants of types. *)
  and 'a type_t =
    | TUnit : 'a type_t
    | TVar : string -> 'a type_t
    | TExists : string -> 'a type_t
    | TForall : string * poly type_t -> poly type_t
    | TFun : 'a type_t * 'a type_t -> 'a type_t

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
  let rec type_subst (t : _ type_t) (n : string) = function
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
  let rec (monotype : 'a type_t -> mono type_t option) = function
    | TUnit -> Some TUnit
    | TVar v -> Some (TVar v)
    | TExists v -> Some (TExists v)
    | TForall _ -> None
    | TFun (u, v) ->
       match (monotype u, monotype v) with
       | (Some u', Some v') -> Some (TFun (u', v'))
       | _ -> None

  (* [polytype t] determines whether a type t is a polytype at runtime. *)
  let rec (polytype : 'a type_t -> poly type_t) = function
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
