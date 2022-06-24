module Iso

public export
record Iso (a, b : Type) where
  constructor MkIso
  to : a -> b
  from : b -> a
  fromTo : (x : a) -> from (to x) = x
  toFrom : (x : b) -> to (from x) = x
