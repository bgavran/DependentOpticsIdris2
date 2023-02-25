module LCCC

import Cats
import Product
import DepAct
import Misc


Slice : (c : Cat) -> (x : obj c) -> Cat
Slice c x = MkCat (a : obj c ** c.arr a x) (\a, b => c.arr (fst a) (fst b))

record HasPullbacks (c : Cat) where
  constructor MkHasPullbacks
  -- This ought to be a cartesian category
  sliceCart : (x : obj c) -> Cartesian (Slice c x)

-- FamProd : (x : Type) -> NonDepAct (Fam TypeCat x) (Fam TypeCat x)
-- FamProd x = MkDepAct $ \x', x'' => \x => (x' x, x'' x)

TypeCatHasPullbacks : HasPullbacks TypeCat
TypeCatHasPullbacks = MkHasPullbacks $ \y => MkCart $ \(x ** f), (y' ** p) => MkProdCone
  ((a :(x, y') ** f (fst a) = p (snd a)) ** f . fst . fst) -- could also do p . snd . fst
  (fst . fst)
  (snd . fst)

-- em : (x : Type) -> Functor (Fam TypeCat x) (Slice TypeCat x)
-- em x = \x' => ((a : x ** x' a) ** fst)

-- me : (x : Type) -> Functor (Slice TypeCat x) (Fam TypeCat x)
-- me x = \sgm => \x => (y : Type ** (x ** ?bnn)) ?eel

SliceInd : (c : Cat) -> HasPullbacks c -> IndCat c
SliceInd c p = MkFunctor (Slice c) lm
  where lm : {x, y : obj c} -> c .arr x y -> Functor (MkCat (a : c .obj ** c .arr a y) (\a => \b => c .arr (a .fst) (b .fst))) (MkCat (a : c .obj ** c .arr a x) (\a => \b => c .arr (a .fst) (b .fst)))
        lm f = MkFunctor
               (\y' => (fst (apex (prod (sliceCart p y) (x ** f) y')) ** proj1 (prod (sliceCart p y) (x ** f) y')))
               (\f => ?mm)
  {-

             y'
             |
             |
             |
             v
  x -------> y



-}


-- reindexing of SliceInd has a right adjoint
public export
record LCCC (c : Cat) where
  constructor MkLCCC
  pbck : HasPullbacks c
  sect : (x : obj c) -> Functor (Slice c x) c

TypeCatLCCC : LCCC TypeCat
TypeCatLCCC = MkLCCC TypeCatHasPullbacks $ \x => MkFunctor
  (\x => DFunction (fst x) (let t = snd x in ?aaa))
  ?bb


