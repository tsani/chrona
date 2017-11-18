module Typecheck

import Context
import Term
import Typing
import Universe

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
       (No contra, _) => No $ \(ty' ** wellTyped') =>
         case wellTyped' of
              Apply _ fw' xw' => contra (_ ** fw')
       (_, No contra) => No $ \(ty' ** wellTyped') =>
         case wellTyped' of
              Apply _ fw' xw' => contra (_ ** xw')
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
