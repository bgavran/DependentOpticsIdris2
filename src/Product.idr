module Product

import Cats

record ProdCone (c : Cat) (x, y : obj c) where
  constructor MkProdCone
  apex : obj c
  proj1 : (arr c) apex x
  proj2 : (arr c) apex y

public export
record Cartesian (c : Cat) where
  constructor MkCart
  prod : (x, y : obj c) -> ProdCone c x y --(xy : obj c ** ((arr c) xy x, (arr c) xy y))
  -- such that...

public export
TypeCatCartesian : Cartesian TypeCat
TypeCatCartesian = MkCart $ \x, y => MkProdCone (x, y) fst snd
