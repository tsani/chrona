module Progress

import Context
import Eval
import EvalContext
import Term
import Typing
import Value
import Universe

%default total
%access public export

||| A shorthand for saying that for a given term t, there exists a term t' and
||| an evaluation context g such that t evaluates to t' under g.
CanStep : (var : Type) -> Term var TYPE -> Type
CanStep var t =
  (t' : Term var TYPE ** g : EvalContext var TYPE ** Eval g t t')

progress : DecEq var =>
           {ctx : Context var TYPE} ->
           {ty : TYPE} ->
           WellTyped ctx t ty ->
           EvalContextFor ectx ctx ->
           Either (IsValue t) (CanStep var t)
progress (Var vctx e) ectxf {ectx} =
  case lookupR ectxf e of
       ((t ** v) ** p) =>
         Right (t ** ectx ** Var (evalContextPreservesValidity ectxf vctx) p)
progress (Zero vctx) ectxf = Left Zero
progress (Succ vctx t') ectxf {ectx} =
  case progress t' ectxf of
       Left v => Left (Succ v)
       Right (t'' ** ectx' ** ev) =>
         let evctx = validContextOf ev in
             Right (Succ t'' ** ectx' ** Succ evctx ev)
progress (Pred vctx t') ectxf {ectx} =
  case progress t' ectxf of
       Left v =>
         let evctx = evalContextPreservesValidity ectxf vctx in
             case v of
                  Zero => Right (Zero ** ectx ** PredZero evctx)
                  Succ v' {t} => Right (t ** ectx ** PredSucc evctx)
                  True => absurd t'
                  False => absurd t'
                  Abstract => absurd t'
       Right (_ ** _ ** ev) =>
         let evctx = validContextOf ev in
             Right (_ ** _ ** Pred evctx ev)
progress (True _) _ = Left True
progress (False _) _ = Left False
progress (IfThenElse vctx cond true false) ectxf =
  case progress cond ectxf of
       Left vCond =>
         let evctx = evalContextPreservesValidity ectxf vctx in
             case vCond of
                  Zero => absurd cond
                  Succ _ => absurd cond
                  True => Right (_ ** _ ** IfThenElseTrue evctx)
                  False => Right (_ ** _ ** IfThenElseFalse evctx)
                  Abstract => absurd cond
       Right (_ ** _ ** ev) =>
           let evctx = validContextOf ev in
               Right (_ ** _ ** IfThenElse evctx ev)
progress (Apply vctx f x) ectxf {ectx} =
  case progress f ectxf of
       Left vf =>
         case progress x ectxf of
              Left vx =>
                case vf of
                     Abstract {param=p} {ty} =>
                       case shadow (p, (_ ** vx)) ectx of
                            (_ ** se) =>
                              let evctx = evalContextPreservesValidity ectxf vctx
                                  in Right (_ ** _ ** Apply evctx vx se)
              Right (_ ** _ ** ev) =>
                let evctx = validContextOf ev in
                    Right (_ ** _ ** ApplyRight evctx vf ev)
       Right (_ ** _ ** ev) =>
         let evctx = validContextOf ev in
             Right (_ ** _ ** ApplyLeft evctx ev)
progress (Abstract s vctx body) ectxf = Left Abstract
