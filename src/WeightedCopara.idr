module WeightedCopara

import Cats
import DepAct

public export
record WeightedCoparaMor
  (c : Cat)
  (m : Cat)
  (ac : NonDepAct c m)
  (s : Functor m TypeCat)
  (A, B : c.obj) where
  constructor MkWCoparaMor
  M : m.obj
  S : s M
  f : c.arr A (ac.act B M)

public export
WeightedCoparaCat : (c : Cat) -> (m : Cat) -> (ac : NonDepAct c m) -> (s : Functor m TypeCat) -> Cat
WeightedCoparaCat c m ac s = MkCat c.obj (WeightedCoparaMor c m ac s)

CoparaCat : (c : Cat) -> (m : Cat) -> (ac : NonDepAct c m) -> Cat
CoparaCat c m ac = WeightedCoparaCat c m ac (constFunctor ())

CoparaCartesian : Cat
CoparaCartesian = CoparaCat TypeCat TypeCat CartAction

CoparaCoCartesian : Cat
CoparaCoCartesian = CoparaCat TypeCat TypeCat CoCartAction


-- h : (arr CoparaCoCartesian) String Bool
-- h = MkWCoparaMor ?m ?s ?f
