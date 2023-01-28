module Cats.Groth

import Cats.Cats
import Cats.Erased

public export
record GrothObj (c : Cat) (d: IndCat c) where
  constructor MkGrothObj
  baseObj : c.obj
  fibObj : (d.mapObj baseObj).obj

public export
record GrothMor (c : Cat) (d : IndCat c) (s : GrothObj c d) (t : GrothObj c d) where
  constructor MkGrothMor
  baseMor : c.arr s.baseObj t.baseObj
  fibMor : (d.mapObj s.baseObj).arr
           s.fibObj
           (d.mapMor {x = s.baseObj} {y = t.baseObj} (baseMor) t.fibObj)

public export
groth : (c : Cat) -> IndCat c -> Cat
groth c ind = MkCat
  (GrothObj c ind)
  (GrothMor c ind)

public export
FLens : (c : Cat) -> (f : IndCat c) -> Cat
FLens c f = groth c (fibOp c f)

public export
DepAdt : Cat
DepAdt = FLens TypeCat Fam0Ind

public export
DLens : Cat
DLens = FLens TypeCat FamInd


-- example of a dependent adapter
f : arr DepAdt (MkGrothObj Nat (Vect0 Bool)) (MkGrothObj Nat (Vect0 Bool))
f = MkGrothMor S (\x => tail0)
