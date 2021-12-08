open Context
open Syntax
module StringSet = Set.Make (String)

type error = [ `SubtypeError of string * poly type_t * poly type_t ]

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
    incr index;
    String.cat prefix suffix

  let reset_index () = index := 0
end

module type TypeChecker = sig
  type err = [ error | Context.error | WellFormed.error ]

  val subtype :
    incomplete_t -> polytype_t -> polytype_t -> (incomplete_t, err) result

  val instL : incomplete_t -> string -> polytype_t -> (incomplete_t, err) result

  val instR : incomplete_t -> polytype_t -> string -> (incomplete_t, err) result

  val check : incomplete_t -> expr_t -> polytype_t -> (incomplete_t, err) result

  val synth : incomplete_t -> expr_t -> (incomplete_t * polytype_t, err) result

  val synthApp :
    incomplete_t ->
    polytype_t ->
    expr_t ->
    (incomplete_t * polytype_t, err) result
end

module MkTypeChecker (State : TypeCheckerState) : TypeChecker = struct
  type err = [ error | Context.error | WellFormed.error ]

  let ( let* ) = Result.bind

  let rec subtype gamma a b =
    let* _ = WellFormed.check_type gamma a in
    let* _ = WellFormed.check_type gamma b in
    match (a, b) with
    (* <:Unit *)
    | TUnit, TUnit -> Ok gamma
    (* <:Var

       Note that the well-formedness checks above already determine
       that both `n` and `m` are members of Γ, this is required as
       denoted by the `Γ[a]` syntax in the original paper.
     *)
    | TVar n, TVar m when n == m -> Ok gamma
    (* <:Exvar

       Similar to <:Var, the well-formedness checks already determine
       that both `n` and `m` are members of Γ.
     *)
    | TExists n, TExists m when n == m -> Ok gamma
    (* <:->

       Notice how we "flip" subtyping in the argument position and in
       the result position. This corresponds to how functions can be
       said to be contravariant in their arguments, and co-variant in
       their return types.

       Simply put, for a function to be a subtype of another function,
       the type of its argument must not be less specific/more generic,
       and its result type must not be more specific/less generic.
     *)
    | TFun (a, b), TFun (x, y) ->
       let* theta = subtype gamma x a in
       subtype theta (apply_context theta b) (apply_context theta y)
    (* <:∀L

       Subtyping for when a forall appears in the left. We start by
       creating an existential type variable, which is used to
       replace all occurences of the bound type variable that the
       forall introduces. After this, we check the premise that this
       substituted type is a subtype of the right type.
     *)
    | TForall (n, t), u ->
       (* We'd like to avoid naming collisions. *)
       let n' = State.fresh_name () in

       let* theta =
         subtype
           (* Γ,>a^,a^ *)
           (gamma |> CMarker n' |> CExists n')
           (* [a^/a]t *)
           (type_subst (TExists n') n t)
           u
       in
       drop_marker (CMarker n') theta
    (* <:R

        Subtyping is much easier when a forall appears on the right.
        More specifically, all we're doing here is removing all bound
        variables introduced by the forall from a type, and then
        checking the premise that our left type is its subtype.
     *)
    | t, TForall (n, u) ->
        let n' = State.fresh_name () in
        let* theta =
          subtype (gamma |> CForall n') t (type_subst (TVar n') n u)
        in
        drop_marker (CForall n') theta
    (* <:InstantiateL

       This performs existential instantiation under two preconditions:
       1. The existential variable appears in the context, i.e. it's
          well-formed
       2. It exists as a bound variable under the `t` type. This means
          that it appears on a forall quantifier.
     *)
    | TExists n, t when not (StringSet.mem n (free_type_vars t)) ->
       instL gamma n t
    (* <:InstantiateR

       This performs existential instantiation under two preconditions:
       1. The existential variable appears in the context, i.e. it's
          well-formed
       2. It exists as a bound variable under the `t` type. This means
          that it appears on a forall quantifier.
     *)
    | t, TExists n when not (StringSet.mem n (free_type_vars t)) ->
       instR gamma t n
    (* Fallthrough *)
    | _, _ -> Error (`SubtypeError ("Invalid case between", a, b))

  and instL _ = failwith "unimplemented"

  and instR _ = failwith "unimplemented"

  and check _ = failwith "unimplemented"

  and synth _ = failwith "unimplemented"

  and synthApp _ = failwith "unimplemented"
end
