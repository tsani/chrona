module Weakening

import Context
import Misc
import Term
import Typing
import Universe

%default total
%access public export

||| If we have a well-typed term in some context, and we shadow that context
||| with a label that doesn't appear in the context, then the term is still
||| well-typed in the new context.
weaken : DecEq var =>
         {lbl : var} ->
         {ctx : Context var TYPE} ->
         NotIn lbl ctx ->
         Shadows (lbl, tp) ctx ctx' ->
         WellTyped ctx t ty ->
         WellTyped ctx' t ty
weaken notIn s (Var vctx e {label}) {lbl} =
  case decEq label lbl of
       Yes Refl => absurd (e, notIn)
       No contra =>
         let e' = shadowPreservesElemNeq contra s e
             vctx' = shadowPreservesValidity vctx s
             in Var vctx' e'
weaken notIn s (Zero vctx) = Zero (shadowPreservesValidity vctx s)
weaken notIn s (Succ vctx w') =
  Succ (shadowPreservesValidity vctx s) (weaken notIn s w')
weaken notIn s (Abstract s' vctx body {ctx'} {pty} {label}) {lbl} {ctx'=c} {tp} =
  case shadow (label, pty) c of
       (ctx'' ** s'') =>
         let vctx' = shadowPreservesValidity vctx s
             in case decEq label lbl of
                  Yes Refl =>
                    case shadowIsFunctional (shadowTrans s s'') s' of
                         Refl => Abstract s'' vctx' body
                  No contra =>
                    let notIn' = shadowPreservesNotIn s' (sym contra) notIn
                        -- notIn'' = shadowPreservesNotIn s (sym contra) notIn
                        -- body' = weaken notIn' ?b body in
                        in Abstract s'' vctx' ?c
                        -- Need: Shadows (lbl, tp) ctx' ctx'' for IH
