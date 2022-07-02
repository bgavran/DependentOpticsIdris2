module Optics

import CartesianLenses

public export
record Optic (A, A', B, B' : Type) where
  constructor MkOptic
  res : Type
  fw : A -> (B, res)
  bw : (res, B') -> A'

CartLensToOptic : {A, A', B, B' : Type} -> CartLens A A' B B' -> Optic A A' B B'
CartLensToOptic (MkCartLens f f') = MkOptic A (\a => (f a, a)) f'
