module Optics.Cartesian

import Lens.Cartesian
import Data.Product
import Data.CoPara
import Data.Para

public export
record Optic (a, b : Boundary) where
  constructor MkOptic
  0 res : Type
  fw : fst a -> (fst b, res)
  bw : (res, snd b) -> snd a

CartLensToOptic : Lens a b -> Optic a b
CartLensToOptic (MkLens f f') = MkOptic (fst a) (graph f) f'

-- alternative definition of optics as CoPara - Para pair where the residuals match
record Optic2 (A, A', B, B' : Type) where
  constructor MkOptic2
  fw : CoPara A B
  bw : Para A B
  resMatch : res fw = res bw
