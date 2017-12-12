h (Nat f) a -> f a -> h g a

why should this be possible? 
the hfunctor h has (Nat f g) in all its recursive positions,
so we should be able to _traverse_ the hfunctor and use the fact that (Nat f)
is an happlicative:
if `phi : Nat f g a`
and `x : f a`
then `phi <**> x : g a`

So if an HTraversable contains an HApplicative, then we can htraverse it!!!
