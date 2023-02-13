module DependentOptics

import DependentLenses
import Optics
import CoPara
import Cats.Erased

public export
record CartDepOptic (A, B : Cont) where
  constructor MkCartDepOptic
  fw : CartDepCoPara (shp A) (shp B)
  bw : (0 a : shp A)
    -> (res1 fw) a -- something over a that acts on it
    -> pos B (fst ((fw1 fw) a)) -- something over f a
    -> pos A a -- something over a
  -- here we're saying that 'a' was used to produce 'b' and isn't anymore available for consumption, but things can still be 'over' it

compDepOptic : {A, B, C : Cont} -> CartDepOptic A B -> CartDepOptic B C -> CartDepOptic A C
compDepOptic f g = MkCartDepOptic
  (compCartDepCoPara (fw f) (fw g))
  (\a0, (r1, r2) => let f' = bw f a0 r1
                        g' = bw g
                        g'b = (erasedReparam (\a => fst (fw1 (fw f) a)) g' a0) r2
                    in f' . g'b)
-- again, lots of things can be simplified outside of Idris

----------------------------------------
-- Embeddings of other kinds of lenses/optics into dependent optics
----------------------------------------

record Unerase (A : Type) (0 a : A) where
  constructor MkUnerase
  a0 : A
  p : a = a0


DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> CartDepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkCartDepOptic
  (MkCartDepCoPara
    (\a => DependentOptics.Unerase (shp A) a)
    (\a => (f a, (MkUnerase a Refl))))
  (\a0, (MkUnerase a p) => ?ee) -- rewrite p in f' a)


ClosedDepLensToCartDepCopara : {A, B : Cont} -> ClosedDepLens A B -> CartDepCoPara (shp A) (shp B)
ClosedDepLensToCartDepCopara (MkClosedDepLens cl) = MkCartDepCoPara
  (\a => (pos B) (fst (cl a)) -> (pos A) a)
  (\a => (fst (cl a) , snd (cl a)))

ClosedDepLensToCartDepOptic : {A, B : Cont} -> ClosedDepLens A B -> CartDepOptic A B
ClosedDepLensToCartDepOptic (MkClosedDepLens cl) = MkCartDepOptic
  (MkCartDepCoPara
  (\a => (pos B) (fst (cl a)) -> (pos A) a)
  (\a => (fst (cl a) , snd (cl a))))
  (\_, f', b' => f' b')


OpticToCartDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' -> CartDepOptic (Const A A') (Const B B')
OpticToCartDepOptic (MkOptic res f f') = MkCartDepOptic
  (MkCartDepCoPara (\_ => res) f)
  (\_ => curry f')


testt : CartDepOptic (Const Double Double) (Const Double Double)
testt = MkCartDepOptic (MkCartDepCoPara (\_ => Double) (\x => (x * x, x))) (\_, x, dy => 2*x*dy)
