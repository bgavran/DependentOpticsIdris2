module CartesianLenses

public export
record CartLens (A, A', B, B' : Type) where
  constructor MkCartLens
  fw : A -> B
  bw : (A, B') -> A'
