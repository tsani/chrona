module Context

import Misc

%default total
%access public export

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

  ||| If we shadow a label that is looked up, then the lookup will now find the
  ||| thing that we shadowed with.
  shadowPreservesElemEq : {ctx : Context var type} ->
                          {typ : type} ->
                          {ty : type} ->
                          Shadows (l, typ) ctx ctx' ->
                          Elem l ty ctx ->
                          Elem l typ ctx'
  shadowPreservesElemEq Here Here = Here
  -- the next case is weird. Basically the Shadows tells us that we've reached
  -- the location where we're replacing the type, but the Elem tells us to look
  -- further. The upshot is that we have an invalid context: the same label can
  -- be found in two different places.
  -- Normally, our contexts are all guarded with ValidContext, so this case is
  -- impossible in particular. This lemma is a bit more general though since we
  -- don't require ValidContext.
  shadowPreservesElemEq Here (There _) = Here
  shadowPreservesElemEq (Skip neq _) Here = absurd (neq Refl)
  shadowPreservesElemEq (Skip _ s) (There e) = There (shadowPreservesElemEq s e)

  ||| If we shadow a label that is not looked up, then the lookup continues to
  ||| find what it used it.
  shadowPreservesElemNeq : {ctx : Context var type} ->
                           {typ : type} ->
                           {ty : type} ->
                           {label : var} ->
                           {l : var} ->
                           (l /= label) ->
                           Shadows (label, typ) ctx ctx' ->
                           Elem l ty ctx ->
                           Elem l ty ctx'
  shadowPreservesElemNeq neq Here Here = absurd (neq Refl)
  shadowPreservesElemNeq neq Here (There e) = There e
  shadowPreservesElemNeq neq (Skip neq' _) Here = Here
  shadowPreservesElemNeq neq (Skip _ s) (There e) =
    There (shadowPreservesElemNeq neq s e)

  shadowPreservesValidity : DecEq lbl =>
                            {label : lbl} ->
                            ValidContext ctx ->
                            Shadows (label, typ) ctx ctx' ->
                            ValidContext ctx'
  shadowPreservesValidity Nil Nil = Nil :: Nil
  shadowPreservesValidity {label} (notIn :: vctx) s {ctx=(lab, ty)::ctx} =
    case decEq label lab of
         Yes Refl => case s of
                          Here => notIn :: vctx
                          Skip neq _ => absurd (neq Refl)
         No neq => case s of
                        Here => absurd (neq Refl)
                        Skip neq' s' =>
                          let ih = shadowPreservesValidity vctx s'
                              in shadowPreservesNotIn s' (sym neq) notIn :: ih
                              -- need: NotIn lab ctx'

  ||| If we shadow a label with a type in some context, then we better be able
  ||| to find that label in the resulting context!
  shadowImpliesElem : {label : var} ->
                      {ty : type} ->
                      {ctx : Context var type} ->
                      Shadows (label, ty) ctx ctx' ->
                      Elem label ty ctx'
  shadowImpliesElem Nil = Here
  shadowImpliesElem Here = Here
  shadowImpliesElem (Skip _ s) = There (shadowImpliesElem s)

  shadowTrans : Shadows (l, x) ctx ctx' ->
                Shadows (l, y) ctx' ctx'' ->
                Shadows (l, y) ctx ctx''
  shadowTrans Nil Nil impossible
  shadowTrans Nil (Skip neq _) = absurd (neq Refl)
  shadowTrans Nil Here = Nil
  shadowTrans (Skip _ _) Nil impossible
  shadowTrans (Skip neq s1) (Skip _ s2) =
    let ih = shadowTrans s1 s2 in Skip neq ih
  shadowTrans (Skip neq _) Here = absurd (neq Refl)
  shadowTrans Here Nil impossible
  shadowTrans Here (Skip neq _) = absurd (neq Refl)
  shadowTrans Here Here = Here

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

