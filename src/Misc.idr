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


-- a non-dependent erased function f : x -> y is a constant fn
-- it factors through x -> () -> y
-- f : (0 x : Int) -> Type
-- f x = ?ee

-- a also must be inhabited
g : ((0 _ : a) -> b) -> a -> () -> b
g f a = \_ => f a

i : b -> ((0 _ : a) -> b)
i b = \_ => b
