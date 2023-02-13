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



public export
record DepParaMor
  (c : Cat)
  (d : IndCat c)
  (m : DepAct c d)
  (A, B : c.obj) where
  constructor MkDepParaMor
  M : (d.mapObj A).obj
  f : c.arr (m.act A M) B

public export
DepParaCat : (c : Cat) -> (d : IndCat c) -> (m : DepAct c d) -> Cat
DepParaCat c d m = MkCat c.obj (DepParaMor c d m)
