module DependentOptics

import CartesianLenses
import DependentLenses
import Optics
import CoPara
import Erased

public export
record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  fw : DepCoPara (shp A) (shp B)
  bw : (0 a : shp A)
    -> (res1 fw) a -- something over a that acts on it
    -> pos B (fst ((fw1 fw) a)) -- something over f a
    -> pos A a -- something over a
  -- here we're saying that 'a' was used to produce 'b' and isn't anymore available for consumption, but things can still be 'over' it

compDepOptic : {A, B, C : Cont} -> DepOptic A B -> DepOptic B C -> DepOptic A C
compDepOptic f g = MkDepOptic
  (compDepCoPara (fw f) (fw g))
  (\a0, (r1, r2) => let f' = bw f a0 r1
                        g' = bw g
                        g'b = (erasedReparam (\a => fst (fw1 (fw f) a)) g' a0) r2
                    in f' . g'b)
-- again, lots of things can be simplified outside of Idris

----------------------------------------
-- Embeddings of other kinds of lenses/optics into dependent optics
----------------------------------------

DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> DepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkDepOptic
  (MkDepCoPara
    (\a => (a0 : shp A ** a = a0))
    (\a => (f a, (a ** Refl))))
  (\a0, (a ** p) => rewrite p in f' a)


ClosedDepLensToDepCopara : {A, B : Cont} -> ClosedDepLens A B -> DepCoPara (shp A) (shp B)
ClosedDepLensToDepCopara (MkClosedDepLens cl) = MkDepCoPara
  (\a => (pos B) (fst (cl a)) -> (pos A) a)
  (\a => (fst (cl a) , snd (cl a)))

ClosedDepLensToDepOptic : {A, B : Cont} -> ClosedDepLens A B -> DepOptic A B
ClosedDepLensToDepOptic (MkClosedDepLens cl) = MkDepOptic
  (MkDepCoPara
  (\a => (pos B) (fst (cl a)) -> (pos A) a)
  (\a => (fst (cl a) , snd (cl a))))
  (\_, f', b' => f' b')


OpticToDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' -> DepOptic (Const A A') (Const B B')
OpticToDepOptic (MkOptic res f f') = MkDepOptic
  (MkDepCoPara (\_ => res) f)
  (\_ => curry f')


testt : DepOptic (Const Double Double) (Const Double Double)
testt = MkDepOptic (MkDepCoPara (\_ => Double) (\x => (x * x, x))) (\_, x, dy => 2*x*dy)
