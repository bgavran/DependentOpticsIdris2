module Cats.Misc

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

public export
record Unerase (A : Type) (0 a : A) where
  constructor MkUnerase
  aRes : A
  p : a = aRes
