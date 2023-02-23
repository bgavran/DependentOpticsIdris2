module WeightedCopara

import Cats
import DepAct

public export
record WeightedCoparaMor
  (c : Cat)
  (m : Cat)
  (ac : NonDepAct c m)
  (s : Functor m (opCat TypeCat)) -- for dep optics s also has to be a monoidal functor (this is because we need to be able to write composition)
  (A, B : c.obj) where
  constructor MkWCoparaMor
  M : m.obj
  S : s.mapObj M
  f : c.arr A ((ac.act B).mapObj M)

public export
WeightedCoparaCat : (c : Cat) -> (m : Cat) -> (ac : NonDepAct c m) -> (0 s : Functor m (opCat TypeCat)) -> Cat
WeightedCoparaCat c m ac s = MkCat c.obj (WeightedCoparaMor c m ac s)

CoparaCat : (c : Cat) -> (m : Cat) -> (ac : NonDepAct c m) -> Cat
CoparaCat c m ac = WeightedCoparaCat c m ac (constType ())

CoparaCartesian : Cat
CoparaCartesian = CoparaCat TypeCat TypeCat CartAction

CoparaCoCartesian : Cat
CoparaCoCartesian = CoparaCat TypeCat TypeCat CoCartAction
