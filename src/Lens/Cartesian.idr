module Lens.Cartesian

import Data.Product

public export
record Lens (a, b : Boundary) where
  constructor MkLens
  fw : fst a -> fst b
  bw : (fst a, snd b) -> snd a

public export
compose : Lens a b -> Lens b c -> Lens a c
compose x y = MkLens
  (y.fw . x.fw)
  (x.bw . fork fst (y.bw . mapFst x.fw))
