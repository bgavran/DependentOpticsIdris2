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


--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Four kinds of F-lenses:
-- Adapters, Dependent adapters
-- Lenses, Dependent lenses
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
DepAdt : Cat
DepAdt = FLens TypeCat Fam0Ind

public export
DepLens : Cat
DepLens = FLens TypeCat FamInd

public export
Lens : Cat
Lens = FLens TypeCat CoKleisliInd

public export
Adt : (c, d : Cat) -> Cat
Adt c d = FLens c (constCat d)


{-
--%%%%%%%%%%%%%%%%%%%%%%%%%--
The rest of the code implements the following four embeddings:



Adt            --> DepAdt       
constCat           Fam0Ind
|                   |
v                   v
Lens  --> DepLens       
CoKleisliInd       FamInd
--%%%%%%%%%%%%%%%%%%%%%%%%%--

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

public export
AdtObjGen : (c : Cat) -> Type
AdtObjGen c = GrothObj c (fibOp c (constCat c))


--- %%%% Four kinds of embeddings, actions on objects
public export
Cont0ToCont : Cont0 -> Cont
Cont0ToCont dd = MkGrothObj dd.baseObj (\a => dd.fibObj a)

public export
AdtObjToConstCont : AdtObj -> ConstCont
AdtObjToConstCont a = MkGrothObj a.baseObj a.fibObj

public export
AdtObjToCont0 : AdtObj -> Cont0
AdtObjToCont0 a = MkGrothObj a.baseObj (\_ => a.fibObj)

public export
ConstContToCont : ConstCont -> Cont
ConstContToCont a = MkGrothObj a.baseObj (\_ => a.fibObj)

--- %%%% Four kinds of embeddings, actions on morphisms
DepAdtToDepLens : {A, B : Cont0}
  -> (arr DepAdt) A B
  -> (arr DepLens) (Cont0ToCont A) (Cont0ToCont B)
DepAdtToDepLens (MkGrothMor f f') = MkGrothMor f (\a => f' a)
-- can't completely eta-reduce because of lack of subtyping of erasable types

LensToDepLens : {A, B : ConstCont}
  -> (arr Lens) A B
  -> (arr DepLens) (ConstContToCont A) (ConstContToCont B)
LensToDepLens (MkGrothMor f f') = MkGrothMor f (curry f') -- hmm we need to curry

AdtToLens : {A, B : AdtObj}
  -> (arr (Adt TypeCat TypeCat)) A B
  -> (arr Lens) (AdtObjToConstCont A) (AdtObjToConstCont B)
AdtToLens (MkGrothMor f f') = MkGrothMor f (\(_, b) => f' b)

AdtToDepAdt : {A, B : AdtObj}
  -> (arr (Adt TypeCat TypeCat)) A B
  -> (arr DepAdt) (AdtObjToCont0 A) (AdtObjToCont0 B)
AdtToDepAdt (MkGrothMor f f') = MkGrothMor f (\_ => f')


{-
This is like object-wise sections of adapters and dependent lenses?
-}
public export
TwistedArr : (c : Cat) -> Cat
TwistedArr c = MkCat
  (p : AdtObjGen c ** c.arr p.baseObj p.fibObj)
  (\a, b => (arr (Adt c c)) (fst a) (fst b))

public export
TwistedArrProj : (c : Cat) -> Functor (TwistedArr c) (Adt c c)
TwistedArrProj c = \(oo ** _) => oo

public export
Dep0TwistedArr : Cat
Dep0TwistedArr = MkCat
  (p : Cont0 ** ((x : p.baseObj) -> (p.fibObj) x)) -- we probably don't need 0 here?
  (\a, b => (arr DepAdt) (fst a) (fst b)) -- + condition that f ; s ; f' = r

public export
Dep0TwistedArrProj : Functor Dep0TwistedArr DepAdt
Dep0TwistedArrProj = \(oo ** _) => oo
