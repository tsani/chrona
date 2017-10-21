module Misc

%default total
%access public export

(/=) : a -> b -> Type
x /= y = Not (x = y)

sym : (a /= b) -> (b /= a)
sym contra Refl = contra Refl
