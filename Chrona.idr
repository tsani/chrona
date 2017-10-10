module Chrona

%default total

(/=) : a -> b -> Type
x /= y = Not (x = y)

sym : (a /= b) -> (b /= a)
sym contra Refl = contra Refl

namespace Context
  data Context : (lbl, ty : Type) -> Type where
    Nil : Context lbl ty
    (::) : (lbl, ty) -> (ctx : Context lbl ty) -> Context lbl ty

  namespace Elem
    data NotIn : lbl -> Context lbl ty -> Type where
      Nil : NotIn label Nil
      (::) : (label /= label') ->
        NotIn label ctx ->
        NotIn label ((label', ty) :: ctx)

    data Elem : lbl -> ty -> Context lbl ty -> Type where
      Here : Elem label ty ((label, ty) :: ctx)
      There : Elem label ty ctx -> Elem label ty ((label', ty') :: ctx)

    Uninhabited (Elem l t Nil) where
      uninhabited Here impossible
      uninhabited (There e) impossible

    Uninhabited (Elem label ty ctx, NotIn label ctx) where
      -- uninhabited : (Elem label ty ctx, NotIn label ctx) -> Void
      uninhabited (e, Nil) = uninhabited e
      uninhabited (Here, (neq :: later)) = neq Refl
      uninhabited (There p, neq :: later) = uninhabited (p, later)

    data DecElem : lbl -> Context lbl ty -> Type where
      Yes : Elem label ty ctx -> DecElem label ctx
      No : NotIn label ctx -> DecElem label ctx

  namespace Valid
    data ValidContext : Context lbl ty -> Type where
      Nil : ValidContext Nil
      (::) : NotIn label ctx ->
        ValidContext ctx ->
        ValidContext ((label, ty) :: ctx)

  namespace Shadow
    ||| Relates two contexts such that the latter is an extension of the former
    ||| with a new (label, type) pair. However, if the input context already
    ||| has the label `label` in it, then its type is rewritten with the new
    ||| type.
    ||| This relation is functional: see the proof shadowIsFunctional.
    data Shadows : (lbl, ty) ->
                   Context lbl ty ->
                   Context lbl ty ->
                   Type where
      Nil : Shadows
        (label, typ)
        Nil
        ( (label, typ) :: Nil )

      Skip : (neq : (label /= label')) ->
             Shadows (label, typ) ctx ctx' ->
             Shadows (label, typ) ((label', typ')::ctx) ((label', typ')::ctx')

      Here : Shadows
        (label, typ)
        ((label, typ') :: ctx) -- label used to have type typ'
        ((label, typ) :: ctx) -- but now it has type typ

    ||| If we have two shadowing relations on the same input context, then they
    ||| must agree on the output context.
    shadowIsFunctional : Shadows p ctx ctx1 ->
                         Shadows p ctx ctx2 ->
                         (ctx1 = ctx2)
    shadowIsFunctional Nil Nil = Refl
    shadowIsFunctional Nil Here impossible
    shadowIsFunctional Nil (Skip _ _) impossible
    shadowIsFunctional Here Nil impossible
    shadowIsFunctional Here Here = Refl
    shadowIsFunctional Here (Skip neq s) = absurd (neq Refl)
    shadowIsFunctional (Skip neq s) Nil impossible
    shadowIsFunctional (Skip neq s) Here = absurd (neq Refl)
    shadowIsFunctional (Skip neq1 s1) (Skip neq2 s2) =
      case shadowIsFunctional s1 s2 of
           Refl => Refl

    ||| If we shadow a label L in some context to get a new context, then the
    ||| shadowing preserves the NotIn relation provided that the label that is
    ||| not in the original context is distinct from the label we're shadowing
    ||| with, since the Shadows relation adds the (label, typ) pair to the
    ||| context if `label` can't be found.
    shadowPreservesNotIn : Shadows (label, typ) ctx ctx' ->
                           (absent /= label) ->
                           NotIn absent ctx ->
                           NotIn absent ctx'
    shadowPreservesNotIn Here _ (neq::later) = (neq::later)
    shadowPreservesNotIn (Skip neq s) n (neq'::later) =
      neq' :: shadowPreservesNotIn s n later
    shadowPreservesNotIn Nil neq Nil = neq :: Nil

    shadowPreservesValidity : DecEq lbl =>
                              (label : lbl) ->
                              ValidContext ctx ->
                              Shadows (label, typ) ctx ctx' ->
                              ValidContext ctx'
    shadowPreservesValidity _ Nil Nil = Nil :: Nil
    shadowPreservesValidity label (notIn :: vctx) s {ctx=(lab, ty)::ctx} =
      case decEq label lab of
           Yes Refl => case s of
                            Here => notIn :: vctx
                            Skip neq _ => absurd (neq Refl)
           No neq => case s of
                          Here => absurd (neq Refl)
                          Skip neq' s' =>
                            let ih = shadowPreservesValidity label vctx s'
                                in shadowPreservesNotIn s' (sym neq) notIn :: ih
                                -- need: NotIn lab ctx'

    shadow : DecEq lbl =>
             (p : (lbl, ty)) ->
             (ctx : Context lbl ty) ->
             (ctx' : Context lbl ty ** Shadows p ctx ctx')
    shadow (label, typ) Nil {lbl} {ty} =
      let ctx' = the (Context lbl ty) ((label, typ) :: Nil)
          s = the (Shadows (label, typ) Nil ctx') Nil
          in (ctx' ** s)
    shadow (label, typ) ((label', typ') :: ctx) {lbl} {ty} =
      case decEq label label' of
           Yes Refl =>
             let ctx' = the (Context lbl ty) ((label, typ) :: ctx)
                 s = the (Shadows (label, typ) ((label, typ') :: ctx) ctx') Here
                 in (ctx' ** s)
           No neq =>
             case shadow (label, typ) ctx of
                  (ctx_ ** s) =>
                    let ctx' = (label', typ') :: ctx_
                        -- vctx'' = notIn :: vctx'
                        s' = Skip neq s
                        in (ctx' ** s')

  ||| If we have two different proofs that the same label are in a valid
  ||| context, then those proofs must agree on what type to assign to the
  ||| variable.
  elemUniqueness : ValidContext ctx ->
                   Elem label ty ctx ->
                   Elem label ty' ctx ->
                   (ty = ty')
  elemUniqueness vctx Here Here = Refl
  elemUniqueness (notIn :: vctx) Here (There p) = absurd (p, notIn)
  elemUniqueness (notIn :: vctx) (There p) Here = absurd (p, notIn)
  elemUniqueness (notIn :: vctx) (There p) (There q) = elemUniqueness vctx p q

  ||| Looks up a label in a valid context.
  decElem : DecEq lbl =>
            {ctx : Context lbl ty} ->
            (label : lbl) ->
            ValidContext ctx ->
            DecElem label ctx
  decElem l Nil = No Nil
  decElem l (nowhere :: vctx) {ctx=(lab, ty)::ctx} =
    case decEq l lab of
         Yes Refl => Yes Here
         No neq => case decElem l vctx of
                           Yes p => Yes (There p)
                           No notIn => No (neq :: notIn)

namespace Term
  data Term : (var : Type) -> (type : Type) -> Type where
    Succ : Term var type -> Term var type
    Zero : Term var type
    True : Term var type
    False : Term var type
    Pred : Term var type -> Term var type
    IfThenElse : (cond : Term var type) ->
                 (true : Term var type) ->
                 (false : Term var type) ->
                 Term var type
    Apply : (fun : Term var type) -> (arg : Term var type) -> Term var type
    Abstract : (param : var) -> (ty : type) -> (body : Term var type) -> Term var type
    Var : var -> Term var type

namespace Typing
  data TYPE = Nat | Bool | Function TYPE TYPE

  ||| Decides whether a type is a function type.
  isFunction : (ty : TYPE) ->
               Dec (p : (TYPE, TYPE) ** (ty = Function (fst p) (snd p)))
  isFunction Nat = No $ \(_ ** Refl) impossible
  isFunction Bool = No $ \(_ ** Refl) impossible
  isFunction (Function s t) = Yes ((s, t) ** Refl)

  DecEq TYPE where
    decEq Nat Nat = Yes Refl
    decEq Nat Bool = No $ \Refl impossible
    decEq Nat (Function _ _) = No $ \Refl impossible
    decEq Bool Nat = No $ \Refl impossible
    decEq Bool Bool = Yes Refl
    decEq Bool (Function _ _) = No $ \Refl impossible
    decEq (Function _ _) Nat = No $ \Refl impossible
    decEq (Function _ _) Bool = No $ \Refl impossible
    decEq (Function s1 t1) (Function s2 t2) =
      case (decEq s1 s2, decEq t1 t2) of
           (Yes Refl, Yes Refl) => Yes Refl
           (Yes Refl, No contra) => No $ \Refl => contra Refl
           (No contra, Yes Refl) => No $ \p => case p of Refl => contra Refl
           (No contra, No _) => No $ \p => case p of Refl => contra Refl

  data WellTyped : Context lbl TYPE -> Term lbl TYPE -> TYPE -> Type where
    Var : ValidContext ctx -> Elem label ty ctx -> WellTyped ctx (Var label) ty
    Zero : ValidContext ctx -> WellTyped ctx Zero Nat
    Succ : ValidContext ctx ->
           WellTyped ctx t Nat ->
           WellTyped ctx (Succ t) Nat
    Pred : ValidContext ctx ->
           WellTyped ctx t Nat ->
           WellTyped ctx (Pred t) Nat
    True : ValidContext ctx ->
           WellTyped ctx True Bool
    False : ValidContext ctx ->
            WellTyped ctx False Bool
    IfThenElse : ValidContext ctx ->
                 WellTyped ctx t Bool ->
                 WellTyped ctx t1 ty ->
                 WellTyped ctx t2 ty ->
                 WellTyped ctx (IfThenElse t t1 t2) ty
    Apply : ValidContext ctx ->
            WellTyped ctx f (Function s t) ->
            WellTyped ctx x s ->
            WellTyped ctx (Apply f x) t
    Abstract : Shadows (label, pty) ctx ctx' ->
               ValidContext ctx ->
               WellTyped ctx' body bty ->
               WellTyped ctx (Abstract label pty body) (Function pty bty)

  ||| Each term has a unique type.
  typeUniqueness : WellTyped ctx t ty1 -> WellTyped ctx t ty2 -> (ty1 = ty2)
  typeUniqueness (Var vctx e) (Var vctx' e') = elemUniqueness vctx e e'
  typeUniqueness (Zero vctx) (Zero vctx') = Refl
  typeUniqueness (Succ vctx t) (Succ vctx' t') = Refl
  typeUniqueness (Pred vctx t) (Pred vctx' t') = Refl
  typeUniqueness (True vctx) (True vctx') = Refl
  typeUniqueness (False vctx) (False vctx') = Refl
  typeUniqueness (IfThenElse vctx e t1 t2) (IfThenElse vctx' e' t1' t2') =
    typeUniqueness t1 t1'
  typeUniqueness (Apply vctx f x) (Apply vctx' f' x') =
    case (typeUniqueness x x', typeUniqueness f f') of
         (Refl, Refl) => Refl
  typeUniqueness
    (Abstract s1 vctx1 body1)
    (Abstract s2 vctx2 body2) =
      case shadowIsFunctional s1 s2 of
           Refl => case typeUniqueness body1 body2 of
                        Refl => Refl

  ||| Given a valid context and an untyped term, decides whether the term is
  ||| well-typed in that context.
  typecheck : DecEq lbl =>
              ValidContext ctx ->
              (term : Term lbl TYPE) ->
              Dec (ty : TYPE ** WellTyped ctx term ty)
  typecheck vctx (Var lbl) =
    case decElem lbl vctx of
         Yes prf {ty} => Yes (ty ** Var vctx prf)
         No notElem => No $ \(ty ** wellTyped) =>
           case wellTyped of
                Var vctx' elem => absurd (elem, notElem)
  typecheck vctx Zero = Yes (Nat ** Zero vctx)
  typecheck vctx (Succ t) =
    case typecheck vctx t of
         Yes (ty ** wellTyped) =>
           case decEq ty Nat of
                Yes Refl => Yes (Nat ** Succ vctx wellTyped)
                No contra => No $ \(ty' ** wellTyped') =>
                  case wellTyped' of
                       Succ _ w => contra (typeUniqueness wellTyped w)
         No contra => No $ \(ty' ** wellTyped') =>
           case wellTyped' of
                Succ vctx w => contra (Nat ** w)
  typecheck vctx True = Yes (Bool ** True vctx)
  typecheck vctx False = Yes (Bool ** False vctx)
  typecheck vctx (Pred t) =
    case typecheck vctx t of
         Yes (ty ** wellTyped) =>
           case decEq ty Nat of
                Yes Refl => Yes (Nat ** Pred vctx wellTyped)
                No contra => No $ \(ty' ** wellTyped') =>
                  case wellTyped' of
                       Pred _ w => contra (typeUniqueness wellTyped w)
         No contra => No $ \(ty' ** wellTyped') =>
           case wellTyped' of
                Pred _ w => contra (Nat ** w)
  typecheck vctx (IfThenElse cond true false) =
    case (typecheck vctx cond, typecheck vctx true, typecheck vctx false) of
         (Yes (cTy ** cW), Yes (trueTy ** trueW), Yes (falseTy ** falseW)) =>
           case (decEq cTy Bool, decEq trueTy falseTy) of
                (Yes Refl, Yes Refl) =>
                  Yes (trueTy ** IfThenElse vctx cW trueW falseW)
                (No contra, _) => No $ \(ty' ** wellTyped') =>
                  case wellTyped' of
                       IfThenElse _ cW' trueW' falseW' =>
                         contra (typeUniqueness cW cW')
                (_, No contra) => No $ \(ty' ** wellTyped') =>
                  case wellTyped' of
                       IfThenElse _ cW' trueW' falseW' =>
                         case (typeUniqueness trueW trueW', typeUniqueness falseW falseW') of
                              (Refl, Refl) => contra Refl
         (No contra, _, _) => No $ \(ty' ** wellTyped') =>
           case wellTyped' of
                IfThenElse _ cW' _ _ => contra (_ ** cW')
         (_, No contra, _) => No $ \(ty' ** wellTyped') =>
           case wellTyped' of
                IfThenElse _ _ trueW' _ => contra (_ ** trueW')
         (_, _, No contra) => No $ \(ty' ** wellTyped') =>
           case wellTyped' of
                IfThenElse _ _ _ falseW' => contra (_ ** falseW')
  typecheck vctx (Apply f x) =
    case (typecheck vctx f, typecheck vctx x) of
         (Yes (fty ** fw), Yes (xty ** xw)) =>
           case isFunction fty of
                Yes ((s, t) ** Refl) =>
                  case decEq xty s of
                       Yes Refl => Yes (t ** Apply vctx fw xw)
                       No contra => No $ \(ty' ** wellTyped') =>
                         case wellTyped' of
                              Apply _ fw' xw' =>
                                case (typeUniqueness xw xw', typeUniqueness fw fw') of
                                     (Refl, Refl) => contra Refl
                No contra => No $ \(ty' ** wellTyped') =>
                  case wellTyped' of
                       Apply _ fw' xw' =>
                         case (typeUniqueness fw' fw, typeUniqueness xw xw') of
                              (Refl, Refl) => contra ((xty, ty') ** Refl)
  typecheck vctx {ctx} (Abstract param ty body) =
    let (ctx' ** s) = shadow (param, ty) ctx
        vctx' = shadowPreservesValidity param vctx s
        in case typecheck vctx' body of
                Yes (wty ** wellTyped) =>
                  Yes (Function ty wty ** Abstract s vctx wellTyped)
                No contra => No $ \(ty' ** wellTyped') =>
                  case wellTyped' of
                       Abstract s' _ bodyW =>
                         case shadowIsFunctional s s' of
                              Refl => contra (_ ** bodyW)
