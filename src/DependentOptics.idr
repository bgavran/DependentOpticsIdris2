module DependentOptics

import CartesianLenses
import DependentLenses
import Optics
import CoPara

sigmaPi : {A, B : Type} -> (A -> (B -> Type)) -> Type
sigmaPi res = (a : A) -> (b : B ** res a b)

record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  res : shp A -> (shp B -> Type)
  fw : sigmaPi res
  bw : {0 a : shp A} -> {0 b : shp B} -> res a b -> pos B b -> pos A a

DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> DepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkDepOptic
  (\a, b => (a0 : shp A ** (a = a0, b = f a)))
  (\a => (f a ** (a  ** (Refl, Refl))))
  (\(a ** (p, q)) => rewrite q in rewrite p in f' a)

OpticToDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' -> DepOptic (Const A A') (Const B B')
OpticToDepOptic (MkOptic res f f') = MkDepOptic (\_, _ => res) ((\(b, r) => (b ** r)) . f) (curry f')

CoParaToDepOptic : {A, B : Type} -> CoPara A B -> DepOptic (Const A ()) (Const B ())
CoParaToDepOptic (MkCoPara m f) = MkDepOptic (\_, _ => m) ((\(b, r) => (b ** r)) . f) (\_, _ => ())

compRes : {A, B, C : Type} -> (A -> (B -> Type)) -> (B -> (C -> Type)) -> (A -> (C -> Type))
compRes r1 r2 = \a, c => (b : B ** (r1 a b, r2 b c))

compDepOptic : {A, B, C : Cont} -> DepOptic A B -> DepOptic B C -> DepOptic A C
compDepOptic (MkDepOptic m f f') (MkDepOptic n g g') = MkDepOptic
  (compRes m n)
  (\a => let (b ** r1) = f a
             (c ** r2) = g b
         in (c ** b ** (r1, r2)))
  (\(b ** (mab, nbc)) => f' mab . g' nbc)

-- dup : (1 x : a) -> (a, a)
-- dup x = (x, ?r)
