module Misc

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

-- only works when the codomain of A' is Type!
public export
DFunction : (A : Type) -> (A' : A -> Type) -> Type
DFunction a a' = (x : a) -> a' x

public export
eval : (a, a -> b) -> b
eval x = (snd x) (fst x)

-- Probably deserves a better name
public export
onlyOne : {a : Type} -> (x : a) -> Type
onlyOne x = (aRes : a ** x = aRes)
