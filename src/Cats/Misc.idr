module Cats.Misc

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)
