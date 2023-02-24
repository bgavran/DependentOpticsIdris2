module Misc

public export

-- only works when the codomain of A' is Type!
public export


-- a non-dependent erased function f : x -> y is a constant fn
-- it factors through x -> () -> y
-- f : (0 x : Int) -> Type
-- f x = ?ee

-- a also must be inhabited
g : ((0 _ : a) -> b) -> a -> () -> b
g f a = \_ => f a

i : b -> ((0 _ : a) -> b)
i b = \_ => b
