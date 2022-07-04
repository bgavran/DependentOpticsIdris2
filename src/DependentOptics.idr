module DependentOptics

import CartesianLenses
import DependentLenses
import Optics
import CoPara

public export
record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  fw : DepCoPara (shp A) (shp B)
  bw : {0 a : shp A} -> {0 b : shp B} -> (res fw) a b -> pos B b -> pos A a

compDepOptic : {A, B, C : Cont} -> DepOptic A B -> DepOptic B C -> DepOptic A C
compDepOptic f g = MkDepOptic
  (compDepCoPara (fw f) (fw g))
  (\(_ ** (mab, nbc)) => (bw f) mab . (bw g) nbc)

----------------------------------------
-- Embeddings of other kinds of lenses/optics into dependent optics
----------------------------------------
DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> DepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkDepOptic
  (MkDepCoPara
    (\a, b => (aRes : shp A ** (a = aRes, b = f a))) (\a => (f a ** a  ** (Refl, Refl))))
  (\(aRes ** (p, q)) => rewrite q in rewrite p in f' aRes)

OpticToDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' -> DepOptic (Const A A') (Const B B')
OpticToDepOptic (MkOptic res f f') = MkDepOptic
  (CoParaToDepCoPara (MkCoPara res f))
  (curry f')

ClosedDepLensToDepOptic : {A, B : Cont} -> ClosedDepLens A B -> DepOptic A B
ClosedDepLensToDepOptic (MkClosedDepLens f) = MkDepOptic
  (MkDepCoPara (\a, b => pos B b -> pos A a) f)
  (\f', b' => f' b')

----------------------------------------

-- coproductMap : {A, B, Z : Cont} -> DepOptic A Z -> DepOptic B Z -> DepOptic (coproduct A B) Z
-- coproductMap (MkDepOptic (MkDepCoPara resl f) f') (MkDepOptic (MkDepCoPara resr g) g') = MkDepOptic
--   (MkDepCoPara
--     (\ab, z with ab
--       | L a = resl a z
--       | R b = resr b z)
--     (\ab => case ab of
--       L a => f a
--       R b => g b))
--   (\t, z' => ?bw)
