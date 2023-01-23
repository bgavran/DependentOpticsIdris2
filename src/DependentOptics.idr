module DependentOptics

import CartesianLenses
import DependentLenses
import Optics
import CoPara

public export
record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  fw : DepCoPara (shp A) (shp B)
  bw : {0 a : shp A} -> {0 b : shp B}
  -> (res fw) a b -> pos B b -> pos A a

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

lemma : (A, B, Z : Cont) ->
        (res1 : (A .shp -> Z .shp -> Type)) ->
        ((a : A .shp) -> (b : Z .shp ** res1 a b)) ->
        ((a : A .shp) -> (b : Z .shp) -> res1 a b -> Z .pos b -> A .pos a) ->
        (res2 : (B .shp -> Z .shp -> Type)) ->
        ((a : B .shp) -> (b : Z .shp ** res2 a b)) ->
        ((a : B .shp) -> (b : Z .shp) -> res2 a b -> Z .pos b -> B .pos a) ->
        (0 a : CoProduct (shp A) (shp B)) -> (0 b : shp Z) ->
        elim res1 res2 a b -> Z .pos b -> elim (A .pos) (B .pos) a
lemma c1 c2 c3 res1 f g res2 f1 g1 a b x y =
  let v = elim' {c = c1.pos} {d = c2.pos} ?dd ?bb in ?lemma_rhs

coproductMap : {A, B, Z : Cont} -> DepOptic A Z -> DepOptic B Z -> DepOptic (coproduct A B) Z
coproductMap (MkDepOptic (MkDepCoPara res1 fw1) bw1) (MkDepOptic (MkDepCoPara res2 fw2) f2) = MkDepOptic
  (MkDepCoPara (elim res1 res2) (\case L x => fw1 x
                                       R x => fw2 x))
  (lemma A B Z res1 fw1 (\_,_ => bw1) res2 fw2 (\_, _ => f2) _ _)
