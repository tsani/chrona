module Eval

import Misc
import Context
import Term
import Typing
import Value

%default total
%access public export

||| We can reuse the Context datatype from earlier, but instead of
||| storing types as associated with labels, we can store *values* for
||| evaluation.
EvalContext : Type -> Type -> Type
EvalContext var ty = Context var (Value var ty)

||| Evaluation rules.
data Eval : EvalContext var ty -> Term var ty -> Term var ty -> Type where
  Var : ValidContext g -> Elem l (v ** prf) g -> Eval g (Var l) v
  Succ : ValidContext g -> Eval g t t' -> Eval g (Succ t) (Succ t')
  Pred : ValidContext g -> Eval g t t' -> Eval g (Pred t) (Pred t')
  PredZero : ValidContext g -> Eval g (Pred Zero) Zero
  PredSucc : ValidContext g -> Eval g (Pred (Succ t)) t
  IfThenElse : ValidContext g ->
               Eval g t t' ->
               Eval g (IfThenElse t true false) (IfThenElse t' true false)
  IfThenElseTrue : ValidContext g -> Eval g (IfThenElse True t1 t2) t1
  IfThenElseFalse : ValidContext g -> Eval g (IfThenElse False t1 t2) t2
  ApplyLeft : ValidContext g -> Eval g t t' -> Eval g (Apply t s) (Apply t' s)
  ApplyRight : ValidContext g -> IsValue v -> Eval g s s' -> Eval g (Apply v s) (Apply v s')
  Apply : ValidContext g ->
          (vPrf : IsValue v) ->
          Shadows (param, (_ ** vPrf)) g g' ->
          Eval g' (Apply (Abstract param ty body) v) body

||| Any evaluation takes place in a valid context.
validContextOf : DecEq var =>
                 {ectx : EvalContext var type} ->
                 Eval ectx t t' ->
                 ValidContext ectx
validContextOf e =
  case e of
       Var v _ => v
       Succ v _ => v
       Pred v _ => v
       PredZero v => v
       PredSucc v => v
       IfThenElse v _ => v
       IfThenElseTrue v => v
       IfThenElseFalse v => v
       ApplyLeft v _ => v
       ApplyRight v _ _ => v
       Apply vctx v s {param} => shadowPreservesValidity param vctx s
