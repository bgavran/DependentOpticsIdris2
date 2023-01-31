module Cats.DepCoPara

import Data.Vect
import Data.DPair

import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.Erased

public export
record DepCoparaMor (c : Cat) (m : DepAct c) (A, B : c.obj) where
  constructor MkDepCoparaMor
  M : (m.bund.mapObj B).obj
  f : c.arr A (m.act B M)
  {-
  (a : A) -> (b : B ** B' b -> A' a)
 -}

public export
DepCoparaCat : (c : Cat) -> (m : DepAct c) -> Cat
DepCoparaCat c m = MkCat c.obj (DepCoparaMor c m)

CoparaCart : Cat
CoparaCart = DepCoparaCat TypeCat CartAction

ClosedLensToCoPara : {A, B, A', B': Type}
-> (A -> (B, B' -> A')) -> (arr CoparaCart) A B
ClosedLensToCoPara cl = MkDepCoparaMor (B' -> A') cl

DepCoparaCart : Cat
DepCoparaCart = DepCoparaCat TypeCat DepCartAction

DepclosedLensToDepCoPara : {A, B : Type} -> {A' : A -> Type} -> {B' : B -> Type}
  -> ((a : A) -> (b : B ** B' b -> A' a)) -> (arr DepCoparaCart) A B
DepclosedLensToDepCoPara cl = MkDepCoparaMor
  (\b => (Exists $ \a0 => (fst (cl a0) = b, B' b -> A' a0)))
  (\a => (fst (cl a) ** (a `Evidence` (Refl, snd (cl a)))))



-- ff : (x -> y) -> (arr DepCoparaCart) x y
-- ff g = (MkDepCoparaMor ?m ?f)

----------------------------------------
-- Examples
----------------------------------------

-- String -> Nat involves an Nat-indexed Set, r:Nat -> Set and then
-- the function f : String -> (n : Nat ** r n)
public export
FamIndDepCopara : DepCoparaMor TypeCat DepCartAction String Nat
FamIndDepCopara = MkDepCoparaMor (flip Vect Bool) (\s => (_ ** map (== 'a') (fromList (unpack s))))

-- String -> Nat involves an Nat-indexed Set, r:Nat -> Set and then
-- the function f : String -> (n : Nat ** r n)
public export
FamInd0DepCopara : DepCoparaMor TypeCat DepCart0Action String Nat
FamInd0DepCopara = MkDepCoparaMor (Vect0 Bool) (\s => (Ev _ (map (== 'a') (fromList (unpack s)))))


-- Example, the graph of a function is a coparameterised morphism
public export
graphCartCoPara : {A, B : Type} -> (A -> B) -> DepCoparaMor TypeCat CartAction A B
graphCartCoPara f = MkDepCoparaMor A (\a => (f a, a))
