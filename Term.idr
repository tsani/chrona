module Term

import Misc

%default total
%access public export

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
