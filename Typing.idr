module Typing

import Misc
import Context
import Term
import Universe

%default total
%access public export

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

Uninhabited (WellTyped ctx True Nat) where
  uninhabited (True _) impossible

Uninhabited (WellTyped ctx False Nat) where
  uninhabited (False _) impossible

Uninhabited (WellTyped ctx (Abstract param ty body) Nat) where
  uninhabited (Abstract _ _ _) impossible

Uninhabited (WellTyped ctx Zero Bool) where
  uninhabited (Zero _) impossible

Uninhabited (WellTyped ctx (Succ t) Bool) where
  uninhabited (Succ _ _) impossible

Uninhabited (WellTyped ctx (Abstract param ty body) Bool) where
  uninhabited (Abstract _ _ _) impossible

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
