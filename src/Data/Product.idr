module Data.Product

-- A pair of types
public export
Boundary : Type
Boundary = (Type, Type)

public export
fork : ((a, b) -> c) -> ((a, b) -> d) -> (a, b) -> (c, d)
fork f g x = (f x, g x)
