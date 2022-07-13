module DependentOptics

import CartesianLenses
import DependentLenses
import Optics
import CoPara
import Utils

public export
record DepOpticCart (A, B : Cont) where
  constructor MkDepOpticCart
  fw : DepCoParaCart (shp A) (shp B)
  bw : {0 a : shp A} -> {0 b : shp B} -> (res fw) a b -> pos B b -> pos A a

compDepOpticCart : {A, B, C : Cont} -> DepOpticCart A B -> DepOpticCart B C -> DepOpticCart A C
compDepOpticCart f g = MkDepOpticCart
  (compDepCoParaCart (fw f) (fw g))
  (\(_ ** (mab, nbc)) => (bw f) mab . (bw g) nbc)



public export
record DepOptic (A, B : Cont) (monProd : Type -> Type -> Type) where
  constructor MkDepOptic
  fw : DepCoPara (shp A) (shp B) monProd
  bw : {0 a : shp A} -> {0 b : shp B} -> monProd ((res fw) a b) (pos B b) -> pos A a


PrismToDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' Either -> DepOptic (Const A A') (Const B B') Either
PrismToDepOptic (MkOptic res f b) = MkDepOptic
  (MkDepCoPara (\_, _ => res) (replace {p=id} (sym $ lemma1 A B res) (mapSnd IsKonst . f)))
  b

compDepOptics : {A, B, C : Cont} -> (monProd : Type -> Type -> Type) -> DepOptic A B monProd -> DepOptic B C monProd -> DepOptic A C monProd
compDepOptics monProd (MkDepOptic (MkDepCoPara r f) f') (MkDepOptic (MkDepCoPara s g) g') = MkDepOptic
  (MkDepCoPara (compRes r s) (replace {p=id} (lemma2 (shp A) (shp C) (compRes r s) monProd) (\a => ?fw)))
  ?bw


{-
----------------------------------------
-- Embeddings of other kinds of lenses/optics into dependent optics
----------------------------------------
public export
DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> DepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkDepOpticCart
  (MkDepCoPara
    (\a, b => (aRes : shp A ** (a = aRes, b = f a))) (\a => (f a ** a  ** (Refl, Refl))))
  (\(aRes ** (p, q)) => rewrite q in rewrite p in f' aRes)

OpticToDepOpticCart : {A, A', B, B' : Type} -> Optic A A' B B' (,) -> DepOpticCart (Const A A') (Const B B')
OpticToDepOptic (MkOptic res f f') = MkDepOpticCart
  (CoParaToDepCoParaCart (MkCoPara res f))
  (curry f')

ClosedDepLensToDepOptic : {A, B : Cont} -> ClosedDepLens A B -> DepOptic A B
ClosedDepLensToDepOptic (MkClosedDepLens f) = MkDepOptic
  (MkDepCoPara (\a, b => pos B b -> pos A a) f)
  (\f', b' => f' b')

----------------------------------------

-- coproductMap : {A, B, Z : Cont} -> DepOptic A Z -> DepOptic B Z -> DepOptic (coproductCont A B) Z
-- coproductMap (MkDepOptic (MkDepCoPara res1 fw1) bw1) (MkDepOptic (MkDepCoPara res2 fw2) f2) = MkDepOptic
--   (MkDepCoPara (elim res1 res2) (\case L x => fw1 x
--                                        R x => fw2 x))
--   (\res, z => ?bw)
