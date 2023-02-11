module Cats.DepCoPara

import Data.Vect
import Data.DPair

import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.Erased

public export
record DepCoparaMor
  (c : Cat)
  (d : IndCat c)
  (m : DepAct c d)
  (A, B : c.obj) where
  constructor MkDepCoparaMor
  M : (d.mapObj B).obj
  f : c.arr A (m.act B M)
  {-
  (a : A) -> (b : B ** B' b -> A' a)
 -}

public export
DepCoparaCat : (c : Cat) -> (d : IndCat c) -> (m : DepAct c d) -> Cat
DepCoparaCat c d m = MkCat c.obj (DepCoparaMor c d m)

public export
CoparaCartesian : Cat
CoparaCartesian = DepCoparaCat TypeCat (constCat TypeCat) (NonDepAct2DepAct CartAction)

-- public export
-- CoparaNewProd : (d : IndCat TypeCat) -> Cat
-- CoparaNewProd d = DepCoparaCat (FLens TypeCat Fam0Ind) (ExtendIndCat TypeCat Fam0Ind d) (e4 (daProdNew d))


{-
DepLensToCoparaNewProd : {A, B : Type}
  -> {A' : (0 _ : A) -> Type}
  -> {B' : (0 _ : B) -> Type}
  -> (arr DepLens) (MkGrothObj A (\a => A' a)) (MkGrothObj B (\b => B' b))
  -> (arr (CoparaNewProd FamInd)) (MkGrothObj A A') (MkGrothObj B B')
DepLensToCoparaNewProd (MkGrothMor f f') = MkDepCoparaMor
  (\_ => A)
  $ MkGrothMor
   (\a => ?fw)
   ?bw

  {-
public export
CoparaNewCoprod : Cat
CoparaNewCoprod = DepCoparaCat (FLens TypeCat Fam0Ind) (ExtendIndCat TypeCat Fam0Ind (constCat TypeCat)) (j4 daCoprod)


PrismToCoparaNew : {A, B, A', B' : Type}
  -> (A -> Either B A')
  -> (B' -> A')
  -> (arr (CoparaNewCoprod)) (MkGrothObj A (\_ => A')) (MkGrothObj B (\_ => B'))
PrismToCoparaNew m b = MkDepCoparaMor
  A'
  $ MkGrothMor
    m
    (\0 a0 => ?bww)

{-
public export
ClosedLensToCoParaNew : {A, B : Type}
  -> {A' : (0 _ : A) -> Type}
  -> {B' : (0 _ : B) -> Type}
  -> ((a : A) -> (b : B ** B' b -> A' a))
  -> (arr CoparaNew) (MkGrothObj A A') (MkGrothObj B B')
ClosedLensToCoParaNew cl = MkDepCoparaMor
  A
  $ MkGrothMor
    (\a => (fst (cl a), a))
    (\0 a0, (aRes, b') => ?bw)


public export
ClosedLensToCoPara : {A, B, A', B': Type}
-> (A -> (B, B' -> A')) -> (arr CoparaCartesian) A B
ClosedLensToCoPara cl = MkDepCoparaMor (B' -> A') cl


DepCoparaCart : Cat
DepCoparaCart = DepCoparaCat TypeCat FamInd (j2 DepCartAction)


{-
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
