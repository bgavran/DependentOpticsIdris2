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
           (d.mapMor {x = s.baseObj} {y = t.baseObj} baseMor t.fibObj)

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
DepLens : Cat
DepLens = FLens TypeCat FamInd

BimorphicLens : Cat
BimorphicLens = FLens TypeCat CoKleisliInd

Adt : Cat
Adt = FLens TypeCat (constCat TypeCat)


{-
The rest of the code implements the following four embeddings:

Adt            --> DepAdt
constCat           Fam0Ind
|                   |
v                   v
BimorphicLens  --> DepLens
CoKleisliInd       FamInd

First there is the verbose bit of mapping betweeen the corresponding objects, then the four embeddings:
-}

--- %%%% Four kinds of objects
public export
Cont : Type
Cont = GrothObj TypeCat (fibOp TypeCat FamInd)

public export
Cont0 : Type
Cont0 = GrothObj TypeCat (fibOp TypeCat Fam0Ind)

public export
ConstCont : Type
ConstCont = GrothObj TypeCat (fibOp TypeCat CoKleisliInd)

public export
AdtObj : Type
AdtObj = GrothObj TypeCat (fibOp TypeCat (constCat TypeCat))


--- %%%% Four kinds of embeddings, actions on objects
public export
Cont0ToCont : Cont0 -> Cont
Cont0ToCont dd = MkGrothObj dd.baseObj (\a => dd.fibObj a)

AdtObjToConstCont : AdtObj -> ConstCont
AdtObjToConstCont a = MkGrothObj a.baseObj a.fibObj

AdtObjToCont0 : AdtObj -> Cont0
AdtObjToCont0 a = MkGrothObj a.baseObj (\_ => a.fibObj)

ConstContToCont : ConstCont -> Cont
ConstContToCont a = MkGrothObj a.baseObj (\_ => a.fibObj)

--- %%%% Four kinds of embeddings, actions on morphisms
DepAdtToDepLens : {A, B : Cont0}
  -> (arr DepAdt) A B
  -> (arr DepLens) (Cont0ToCont A) (Cont0ToCont B)
DepAdtToDepLens (MkGrothMor f f') = MkGrothMor f (\a => f' a)
-- can't completely eta-reduce because of lack of subtyping of erasable types

BimorphicLensToDepLens : {A, B : ConstCont}
  -> (arr BimorphicLens) A B
  -> (arr DepLens) (ConstContToCont A) (ConstContToCont B)
BimorphicLensToDepLens (MkGrothMor f f') = MkGrothMor f (curry f') -- hmm we need to curry

AdtToBimorphicLens : {A, B : AdtObj}
  -> (arr Adt) A B
  -> (arr BimorphicLens) (AdtObjToConstCont A) (AdtObjToConstCont B)
AdtToBimorphicLens (MkGrothMor f f') = MkGrothMor f (\(_, b) => f' b)

AdtToDepAdt : {A, B : AdtObj}
  -> (arr Adt) A B
  -> (arr DepAdt) (AdtObjToCont0 A) (AdtObjToCont0 B)
AdtToDepAdt (MkGrothMor f f') = MkGrothMor f (\_ => f')
