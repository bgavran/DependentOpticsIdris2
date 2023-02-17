module Misc

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

public export
Section : (A : Type) -> (A' : A -> Type) -> Type
Section a a' = (x : a) -> a' x
