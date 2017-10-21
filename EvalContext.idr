module EvalContext

import Context
import Eval
import Misc
import Term
import Typing
import Value
import Universe

%default total
%access public export

||| An evaluation context is related to a typing context if they use the same
||| labels.
data EvalContextFor : EvalContext var type -> Context var type -> Type where
  Nil : EvalContextFor Nil Nil
  (::) : WellTyped Nil t ty ->
         EvalContextFor ectx ctx ->
         EvalContextFor ((lab, (t ** vPrf)) :: ectx) ((lab, ty) :: ctx)

data Elem : {ctx : Context var type} -> (lbl : var) -> EvalContextFor ectx ctx -> Type where
  Here : Elem lab ((::) {lab} w ectxf)
  There : Elem lab ectxf -> Elem lab (w :: ectxf)

-- shadowPreservesEvalContextFor : Shadows (lbl, ty) ctx ctx' ->
--                                 Shadows (lbl, v) ectx ectx' ->
--                                 EvalContextFor ectx ctx ->
--                                 EvalContextFor ectx' ctx'
-- shadowPreservesEvalContextFor Nil Nil Nil =
--   Add Nil
-- shadowPreservesEvalContextFor (Skip neq _) Here (Add _) =
--   absurd (neq Refl)
-- shadowPreservesEvalContextFor Here (Skip neq _) (Add _) =
--   absurd (neq Refl)
-- shadowPreservesEvalContextFor
--   (Skip neq1 s1)
--   (Skip neq2 s2)
--   (Add ectxf) = Add (shadowPreservesEvalContextFor s1 s2 ectxf)
-- shadowPreservesEvalContextFor Here Here (Add ectxf) = Add ectxf

||| The evaluation context corresponding to a typing context preserves the Elem
||| relation.
||| Another way to think of this function is that it looks up the value
||| associated with the label in the evaluation context.
evalContextPreservesElemR : {label : var} ->
                            {ty : type} ->
                            EvalContextFor ectx ctx ->
                            Elem label ty ctx ->
                            (v : Value var type ** Elem label v ectx)
evalContextPreservesElemR Nil e = absurd e
evalContextPreservesElemR ((::) _ ectxf {vPrf}) Here = ((_ ** vPrf) ** Here)
evalContextPreservesElemR ((::) _ ectxf) (There e) =
  case evalContextPreservesElemR ectxf e of
       (val ** e') => (val ** There e')

promoteRight : Elem label ty ctx ->
               (ectxf : EvalContextFor ectx ctx) ->
               Elem label ectxf
promoteRight Here (_ :: _) = Here
promoteRight (There e) (_ :: ectxf) = There (promoteRight e ectxf)

promoteLeft : Elem label ty ectx ->
              (ectxf : EvalContextFor ectx ctx) ->
              Elem label ectxf
promoteLeft Here (_ :: _) = Here
promoteLeft (There e) (_ :: ectxf) = There (promoteLeft e ectxf)

evalContextPreservesElemL : {label : var} ->
                            {ctx : Context var type} ->
                            EvalContextFor ectx ctx ->
                            Elem label val ectx ->
                            (ty : type ** Elem label ty ctx)
evalContextPreservesElemL Nil e = absurd e
evalContextPreservesElemL ((::) _ ectxf {ty}) Here = (ty ** Here)
evalContextPreservesElemL ((::) _ ectxf) (There e) =
  case evalContextPreservesElemL ectxf e of
       (ty ** e') => (ty ** There e')

evalContextPreservesNotIn : {ctx : Context var ty} ->
                            {ectx : EvalContext var ty} ->
                            {label : var} ->
                            EvalContextFor ectx ctx ->
                            NotIn label ctx ->
                            NotIn label ectx
evalContextPreservesNotIn Nil Nil = Nil
evalContextPreservesNotIn (_ :: ectxf) (neq :: notLater) =
  neq :: evalContextPreservesNotIn ectxf notLater

evalContextPreservesValidity : EvalContextFor ectx ctx ->
                               ValidContext ctx ->
                               ValidContext ectx
evalContextPreservesValidity Nil Nil = Nil
evalContextPreservesValidity (_ :: ectxf) (notIn :: vctx) =
  let ih = evalContextPreservesValidity ectxf vctx in
      evalContextPreservesNotIn ectxf notIn :: ih

lookupR : {label : var} ->
          {ty : type} ->
          EvalContextFor ectx ctx ->
          Elem label ty ctx ->
          (v : Value var type ** Elem label v ectx)
lookupR = evalContextPreservesElemR

lookupL : {label : var} ->
          {ctx : Context var type} ->
          EvalContextFor ectx ctx ->
          Elem label v ectx ->
          (ty : type ** Elem label ty ctx)
lookupL = evalContextPreservesElemL

lookupBoth : {label : var} ->
             {ctx : Context var TYPE} ->
             {ty : TYPE} ->
             Elem label ty ctx ->
             Elem label (t ** vPrf) ectx ->
             ValidContext ctx ->
             ValidContext ectx ->
             EvalContextFor ectx ctx ->
             WellTyped Nil t ty
lookupBoth Here Here _ _ ((::) w _) = w
lookupBoth (There e1) (There e2) (_ :: vctx) (_ :: vectx) (_ :: ectxf) =
  lookupBoth e1 e2 vctx vectx ectxf
lookupBoth Here (There e) (notInT :: _) _ (_ :: ectxf) =
  case lookupL ectxf e of
       (_ ** e') => absurd (e', notInT)
lookupBoth (There e) Here _ (notInE :: _) (_ :: ectxf) =
  case lookupR ectxf e of
       (_ ** e') => absurd (e', notInE)

lookup : {label : var} ->
         {ctx : Context var TYPE} ->
         (ectxf : EvalContextFor ectx ctx) ->
         Elem label ectxf ->
         (t : Term var TYPE ** ty : TYPE ** (WellTyped Nil t ty, IsValue t))
lookup ((::) w _ {vPrf}) Here = (_ ** _ ** (w, vPrf))
lookup (_ :: ectxf) (There e) = lookup ectxf e
