module Cats.DepPara

import Data.Vect
import Data.DPair

import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.Erased

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
