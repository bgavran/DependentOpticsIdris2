module Optics

import CartesianLenses
import CoPara
import Para

public export
record Optic (A, A', B, B' : Type) where
  constructor MkOptic
  res : Type
  fw : A -> (B, res)
  bw : (res, B') -> A'

CartLensToOptic : {A, A', B, B' : Type} -> CartLens A A' B B' -> Optic A A' B B'
CartLensToOptic (MkCartLens f f') = MkOptic A (graph f) f'

-- alternative definition of optics as CoPara - Para pair where the residuals match
{-
record Optic2 (A, A', B, B' : Type) where
  constructor MkOptic2
  fw : CoPara A B
  bw : Para A B
  resMatch : res fw = res bw
-}
