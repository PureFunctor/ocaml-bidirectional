open Context
open Syntax
module StringSet = Set.Make (String)

type error =
  [ `SubtypeError of polytype_t * polytype_t
  | `CannotInstantiate of string * polytype_t
  | `CannotSynthesize of expr_t
  | `ImpossibleCase
  ]

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
  type err = [ error | Context.error | Syntax.error ]

  val subtype :
    incomplete_t -> polytype_t -> polytype_t -> (incomplete_t, err) result

  val instL : incomplete_t -> string -> polytype_t -> (incomplete_t, err) result

  val instR : incomplete_t -> polytype_t -> string -> (incomplete_t, err) result

  val check : incomplete_t -> expr_t -> polytype_t -> (incomplete_t, err) result

  val synth : incomplete_t -> expr_t -> (incomplete_t * polytype_t, err) result

  val synth_app :
    incomplete_t ->
    polytype_t ->
    expr_t ->
    (incomplete_t * polytype_t, err) result
end

module MkTypeChecker (State : TypeCheckerState) : TypeChecker = struct
  type err = [ error | Context.error | Syntax.error ]

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
    | _, _ -> Error (`SubtypeError (a, b))

  and instL gamma alpha a =
    let* _ = WellFormed.check_type gamma a in
    (* InstLSolve

       The premise for this rule states that existential type variables
       can only be instantiated using monotypes. If we don't meet this
       condition, we'll have to perform the alternatives below.
     *)
    match Result.bind (Syntax.monotype a) (solve_context gamma alpha) with
    | Ok gamma' -> Ok gamma'
    | Error _ ->
        match a with
        (* InstLReach

           When instantiating to another existential, we simply point
           that other existential to the current one being solved.
         *)
        | TExists beta -> solve_context gamma beta (TExists alpha)
        (* InstLArr

           This performs instantiation for functions with respect to the
           variance of its components. As mentioned earlier, arguments
           are contravariant while result types are covariant. This
           means that we need to instantiate the argument type into
           a subtype of an existential, while we need to instantiate an
           existential into a subtype of the result type.
         *)
        | TFun (a, b) ->
            let alpha' = State.fresh_name () in
            let beta' = State.fresh_name () in

            let* gamma' =
              insert_at gamma (CExists alpha)
                (empty
                 |> CExists beta'
                 |> CExists alpha'
                 |> CSolved (alpha, TFun (TExists alpha', TExists beta')))
            in
            let* theta =
              instR gamma' a alpha'
            in

            instL theta beta' (apply_context theta b)
        (* InstLAllR

           This rule performs instantiation of universally quantified
           types. In order to recurse, we replace all occurances of the
           bound variable with an existential.
         *)
        | TForall (beta, b) ->
           let beta' = State.fresh_name () in

           let* delta =
             instL
               (gamma |> CForall beta')
               alpha
               (type_subst (TVar beta') beta b)
           in

           drop_marker (CForall beta') delta
        | _ ->
           Error (`CannotInstantiate (alpha, a))

  and instR gamma a alpha =
    let* _ = WellFormed.check_type gamma a in
    (* InstRSolve

       This is practically the same as instL, but with some of the
       instantiations flipped around.
     *)
    match Result.bind (monotype a) (solve_context gamma alpha) with
    | Ok gamma' -> Ok gamma'
    | Error _ ->
       match a with
       (* InstRReach *)
       | TExists beta -> solve_context gamma beta (TExists alpha)
       (* InstRArr *)
       | TFun (a, b) ->
           let alpha' = State.fresh_name () in
           let beta' = State.fresh_name () in

           let* gamma' =
             insert_at gamma (CExists alpha)
               (empty
                |> CExists beta' |> CExists alpha'
                |> CSolved (alpha, TFun (TExists alpha', TExists beta')))
           in
           let* theta =
             instL gamma' alpha' a
           in

           instR theta (apply_context theta b) beta'
       (* InstRAllL *)
       | TForall (beta, b) ->
           let beta' = State.fresh_name () in

           let* theta =
             instL
               (gamma |> CMarker beta' |> CExists beta')
               beta'
               (type_subst (TExists beta') beta b)
           in

           drop_marker (CMarker beta') theta
       | _ ->
          Error (`CannotInstantiate (alpha, a))

  and check gamma e t =
    let* _ = WellFormed.check_type gamma t in
    match (e, t) with
    (* 1I

       Literal types check against their corresponding types.
     *)
    | EUnit, TUnit -> Ok gamma
    (* ∀I

       Unwraps a quantified type variable, renames all occurences of
       its bound type variable with a new name, and recursively type
       checks.
     *)
    | _, TForall (a, t) ->
       let a' = State.fresh_name () in

       let* theta =
         check (gamma |> CForall a') e (type_subst (TVar a') a t)
       in

       drop_marker (CForall a') theta
    (* ->I

       Type checking a lambda abstraction involves creating a context
       where the bound variable is annotated by the argument type, in
       order to type check the lambda body against the return type.
     *)
    | EAbs (a, b), TFun (a_t, b_t) ->
       let a' = State.fresh_name () in

       let* theta =
        check (gamma |> CVar (a', a_t)) (expr_subst (EVar a') a b) b_t
       in

       drop_marker (CVar (a', a_t)) theta
    (* Fallthrough.

       Most cases should be solvable by synthesizing the type of an
       expression and asserting that it's a subtype of the expected
       type.
     *)
    | _ ->
       let* (theta, polytype) = synth gamma e in
       subtype theta (apply_context theta polytype) (apply_context theta t)

  and synth gamma e =
    let* _ = WellFormed.check_context gamma in
    match e with
    (* 1I=>

       Literal types synthesize to their corresponding types.
     *)
    | EUnit ->
       Ok (gamma, TUnit)

    (* Var=>

       Synthesizing variables involve looking up the `CVar` element
       in the context.
     *)
    | EVar a ->
       let find_var = function
         | CVar (b, t) when a = b -> Some t
         | _ -> None
       in
       (match List.find_map find_var gamma with
       | Some t -> Ok (gamma, t)
       | None -> Error (`CannotSynthesize e))

    (* I=>

       Damas-Hindley-Milner Type Inference, adapted from
       https://github.com/ollef/Bidirectional

       Unlike the original rule described in the paper, this allows
       functions to synthesize in a polymorphic manner. Instead of
       producing `a^ -> b^`, this produces `forall a b. a -> b`.
     *)
    | EAbs (a, b) ->
       let a' = State.fresh_name () in

       let alpha = State.fresh_name () in
       let beta = State.fresh_name () in

       let* theta =
         check
           (gamma
            |> CMarker alpha
            |> CExists alpha
            |> CExists beta
            |> CVar (a', (TExists alpha)))
           (expr_subst (EVar a') a b)
           (TExists beta)
       in

       let* (gammaL, gammaR) = break_at (CMarker alpha) theta in

       let tau = apply_context gammaL (TFun (TExists alpha, TExists beta)) in
       let uns = collect_unsolved gammaL in
       let uvr = List.init (List.length uns) (fun _ -> State.fresh_name ()) in
       let sbt = List.fold_right (fun (n', n) t -> type_subst (TVar n') n t) (List.combine uvr uns) tau in
       Ok (gammaR, List.fold_right (fun a b -> TForall (a, b)) uvr sbt)
    (* ->E

       Type synthesis for function application is implemented as
       in the `synth_app` function.
     *)
    | EApp (f, x) ->
       let* (theta, polytype) = synth gamma f in
       synth_app theta (apply_context theta polytype) x
    (* =>Ann

       This is here because of the catch-all clause present in the
       `check` type. A keen eye may notice that most of the driving
       work for the type checking algorithm actually involves subtyping,
       instantiation, and synthesis.

       As it turns out, as long as you can synthesize the type of some
       expression, you can check whether it's a subtype
     *)
    | EAnn (e', t) -> let* theta = check gamma e' t in Ok (theta, t)

  and synth_app gamma t e =
    let* _ = WellFormed.check_type gamma t in
    match t with
    (* ∀App

       Unwraps the quantified type, replaces all occurances of bound
       variables with existentials, and recurses further.
     *)
    | TForall (a, t) ->
       let a' = State.fresh_name () in
       synth_app (gamma |> CExists a') (type_subst (TExists a') a t) e
    (* a^App

       When an existential variable is being applied, two new
       existential type variables are introduced: one for the argument
       type and one for the result type.

       The argument is first checked against the argument existential,
       leading into synthesis, then subtyping, then eventually
       instantiation, after which the result existential is returned
       to be solved down the line.
     *)
    | TExists a ->
        let a' = State.fresh_name () in
        let b' = State.fresh_name () in

        let* gamma' =
          insert_at gamma (CExists a)
            (empty
             |> CExists b'
             |> CExists a'
             |> CSolved (a, (TFun ((TExists a'), (TExists b')))))
        in
        let* delta =
          check gamma' e (TExists a')
        in
        Ok (delta, TExists b')
    (* ->App

       Vanilla application synthesis. As long as the argument checks
       against the argument type, this case proceeds just fine.
     *)
    | TFun (a, b) ->
        let* delta = check gamma e a in
        Ok (delta, b)
    | _ ->
       Error `ImpossibleCase
end

module T = MkTypeChecker(MkTypeCheckerState())
