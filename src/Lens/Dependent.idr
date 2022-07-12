module Lens.Dependent

import Data.Container
import Data.Coproduct
import Data.Product
import Lens.Cartesian

public export
record DepLens (a, b : Cont) where
  constructor MkDepLens
  fw : a.shp -> b.shp
  bw : (x : a.shp) -> b.pos (fw x) -> a.pos x

CartLensToDepLens : Cartesian.Lens a b -> DepLens (Const (fst a) (snd a)) (Const (fst b) (snd b))
CartLensToDepLens (MkLens f f') = MkDepLens f (curry f')

public export
record ClosedDepLens (A, B : Cont) where
  constructor MkClosedDepLens
  f : (a : shp A) -> (b : shp B ** pos B b -> pos A a)

coproductMap : {0 A, B, Z : Cont} -> DepLens A Z -> DepLens B Z -> DepLens (coproduct A B) Z
coproductMap (MkDepLens f f') (MkDepLens g g') = MkDepLens
  (\ab => case ab of
    L a => f a
    R b => g b)
  (\ab => case ab of
    L a => f' a
    R b => g' b)
