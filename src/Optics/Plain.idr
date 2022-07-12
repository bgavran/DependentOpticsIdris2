module Optics.Plain

import Data.Coproduct
import Data.Product

public export
record PlainOptics (Rel : Type -> Type -> Type) (a, b : Boundary) where
  constructor MkPlainOptic
  0 r : Type
  fw : fst a -> r `Rel` fst b
  bw : r `Rel` snd b -> snd a

-- lenses
export
composeCartesianOptics : PlainOptics Pair a b -> PlainOptics Pair b c -> PlainOptics Pair a c
composeCartesianOptics x y = MkPlainOptic
  (Pair x.r y.r)
  (\a => let v = x.fw a; w = y.fw (snd v) in ((fst v, fst w), snd w))
  (\case ((z, v), w) => x.bw (z , (y.bw (v, w))))

-- prisms
export
composeCocartesianOptics : PlainOptics (+) a b -> PlainOptics (+) b c -> PlainOptics (+) a c
composeCocartesianOptics x y = MkPlainOptic
  (x.r + y.r)
  (elim (L . L) (mapFst R . y.fw) . x.fw)
  (x.bw . elim (mapSnd (y.bw . L)) (R . y.bw . R ))
