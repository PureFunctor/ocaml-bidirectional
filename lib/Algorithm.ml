open Context
open Syntax
module StringSet = Set.Make (String)

module type TypeCheckerState = sig
  val index : int ref

  val fresh_name : unit -> string

  val reset_index : unit -> unit
end

module MkTypeCheckerState () : TypeCheckerState = struct
  let index = ref 0

  let fresh_name () =
    let prefix = String.make 1 (Char.chr (97 + (!index / 26))) in
    let suffix = string_of_int (!index mod 26) in
    let _ = index := !index + 1 in
    String.cat prefix suffix

  let reset_index () = index := 0
end

module type TypeChecker = sig
  val subtype :
    incomplete Context.t -> poly type_t -> poly type_t -> incomplete Context.t

  val instL :
    incomplete Context.t -> string -> poly type_t -> incomplete Context.t

  val instR :
    incomplete Context.t -> poly type_t -> string -> incomplete Context.t

  val check :
    incomplete Context.t -> expr_t -> poly type_t -> incomplete Context.t

  val synth :
    incomplete Context.t -> expr_t -> incomplete Context.t * poly type_t

  val synthApp :
    incomplete Context.t ->
    poly type_t ->
    expr_t ->
    incomplete Context.t * poly type_t
end

module MkTypeChecker (State : TypeCheckerState) : TypeChecker = struct
  let rec subtype gamma a b =
    assert (WellFormed.check_type gamma a);
    assert (WellFormed.check_type gamma b);
    match (a, b) with
    | TUnit, TUnit -> gamma
    | TVar n, TVar m when n == m -> gamma
    | TExists n, TExists m when n == m -> gamma
    | TFun (a, b), TFun (x, y) ->
        let theta = subtype gamma x a in
        subtype theta (apply_context theta b) (apply_context theta y)
    | t, TForall (n, u) ->
        let n' = State.fresh_name () in
        let gamma' = gamma |> CForall n' in
        let u' = type_subst (TVar n') n u in
        let theta = subtype gamma' t u' in
        drop_marker (CForall n') theta
    | TForall (n, t), u ->
        let n' = State.fresh_name () in
        let gamma' = gamma |> CMarker n' |> CExists n' in
        let t' = type_subst (TExists n') n t in
        let theta = subtype gamma' t' u in
        drop_marker (CMarker n') theta
    | t, TExists n
      when List.memq n (collect context_existentials gamma)
           && not (StringSet.mem n (free_type_vars t)) ->
        instL gamma n t
    | TExists n, t
      when List.memq n (collect context_existentials gamma)
           && not (StringSet.mem n (free_type_vars t)) ->
        instR gamma t n
    | _, _ -> failwith "Cannot solve subtypes."

  and instL _ = failwith "unimplemented"

  and instR _ = failwith "unimplemented"

  and check _ = failwith "unimplemented"

  and synth _ = failwith "unimplemented"

  and synthApp _ = failwith "unimplemented"
end
