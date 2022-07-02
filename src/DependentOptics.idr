module DependentOptics

import CartesianLenses
import DependentLenses
import Optics
import CoPara

record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  fw : DepCoPara (shp A) (shp B)
  bw : {0 a : shp A} -> {0 b : shp B} -> (res fw) a b -> pos B b -> pos A a

DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> DepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkDepOptic
  (MkDepCoPara
    (\a, b => (a0 : shp A ** (a = a0, b = f a))) (\a => (f a ** (a  ** (Refl, Refl)))))
  (\(a ** (p, q)) => rewrite q in rewrite p in f' a)

OpticToDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' -> DepOptic (Const A A') (Const B B')
OpticToDepOptic (MkOptic res f f') = MkDepOptic
  (CoParaToDepCoPara (MkCoPara res f))
  (curry f')

compDepOptic : {A, B, C : Cont} -> DepOptic A B -> DepOptic B C -> DepOptic A C
compDepOptic (MkDepOptic f f') (MkDepOptic g g') = MkDepOptic
  (MkDepCoPara (compRes (res f) (res g))
  (\a => let (b ** r1) = (fw f) a
             (c ** r2) = (fw g) b
         in (c ** b ** (r1, r2))))
  (\(b ** (mab, nbc)) => f' mab . g' nbc)

-- dup : (1 x : a) -> (a, a)
-- dup x = (x, ?r)
