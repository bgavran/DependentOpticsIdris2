module Cats.DepOptics

import Data.DPair

import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.DepCoPara
import Cats.Erased

-- Dependent optics is CoPara of something
-- CoPara(Cont)
public export
DependentOpticsCat : (c : Cat) -> (m : DepAct c) -> (d : IndCat c)
  -> (over : OverDepAct c m d)
  -> Cat
DependentOpticsCat c m d over = DepCoparaCat (FLens c d) (GrothAct c m d over)

public export
CartDepOptic : Cat
CartDepOptic = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct

public export
CartDepOptic0 : Cat
CartDepOptic0 = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct -- no 0s

i : {A : Type} -> ((0 _ : A) -> Type) -> (A -> Type)
i f a = f a

public export
DepLensToDepOptic : (A, B : Type)
  -> (A' : A -> Type)
  -> (B' : B -> Type)
  -> (arr DLens) (MkGrothObj A (A')) (MkGrothObj B (B'))
  -> (arr CartDepOptic0) (MkGrothObj A A') (MkGrothObj B B')
DepLensToDepOptic a b a' b' (MkGrothMor f f') = MkDepCoparaMor
  ?rr
  (MkGrothMor (\a => ?ff) ?bw)
  {-
  (\bVal => (a `Subset0` (\a0 => f a0 = bVal)))
  (MkGrothMor (\a => Ev (f a) (El a Refl)) lemmaFinal)
  where lemmaFinal : (0 x : a) -> (b' (f x), Subset0 a (\0 a0 => f a0 = f x)) -> a' x
        lemmaFinal x0 (b', (El aRes p)) = let t = f' aRes (rewrite p in b') in ?bw
        -}


DepclosedLensToDepOptic : (A, B : Type)
  -> (A' : A -> Type)
  -> (B' : B -> Type)
  -> ((a : A) -> (b : B ** B' b -> A' a))
  -> (arr CartDepOptic) (MkGrothObj A A') (MkGrothObj B B')
DepclosedLensToDepOptic a b a' b' cl = MkDepCoparaMor
  (\bVal => (Exists $ \a0 => (fst (cl a0) = bVal, b' bVal -> a' a0)))
  (MkGrothMor (\a => (fst (cl a) ** a `Evidence` (Refl, snd (cl a))))
  (\x => ?bww))
