module Optics

import CartesianLenses
import CoPara
import Para

public export
record Optic (A, A', B, B' : Type) (monProd : Type -> Type -> Type) where
  constructor MkOptic
  res : Type
  fw : A -> monProd B res
  bw : monProd res B' -> A'

CartLensToCartOptic : {A, A', B, B' : Type} -> CartLens A A' B B' -> Optic A A' B B' (,)
CartLensToCartOptic (MkCartLens f f') = MkOptic A (graph f) f'

-- alternative definition of optics as CoPara - Para pair where the residuals match
record Optic2 (A, A', B, B' : Type) (monProd : Type -> Type -> Type) where
  constructor MkOptic2
  fw : CoPara A B monProd
  bw : Para A B monProd
  resMatch : res fw = res bw
