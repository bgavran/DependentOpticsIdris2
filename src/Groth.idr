module Groth

import Cats
import Erased
import Data.Vect

public export

public export

public export

public export


--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Four kinds of F-lenses:
-- Adapters, Dependent adapters
-- Lenses, Dependent lenses
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export

public export

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

public export

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
  -> (arr (DepAdt TypeCat)) A B
  -> (arr (DepLens TypeCat)) (Cont0ToCont A) (Cont0ToCont B)
DepAdtToDepLens (MkGrothMor f f') = MkGrothMor f (\a => f' a)
-- can't completely eta-reduce because of lack of subtyping of erasable types

LensToDepLens : {A, B : ConstCont}
  -> (arr Lens) A B
  -> (arr (DepLens TypeCat)) (ConstContToCont A) (ConstContToCont B)
LensToDepLens (MkGrothMor f f') = MkGrothMor f (curry f') -- hmm we need to curry

AdtToLens : {A, B : AdtObj}
  -> (arr (Adt TypeCat TypeCat)) A B
  -> (arr Lens) (AdtObjToConstCont A) (AdtObjToConstCont B)
AdtToLens (MkGrothMor f f') = MkGrothMor f (\(_, b) => f' b)

AdtToDepAdt : {A, B : AdtObj}
  -> (arr (Adt TypeCat TypeCat)) A B
  -> (arr (DepAdt TypeCat)) (AdtObjToCont0 A) (AdtObjToCont0 B)
AdtToDepAdt (MkGrothMor f f') = MkGrothMor f (\_ => f')


--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Testing, example
--%%%%%%%%%%%%%%%%%%%%%%%%%--

X' : Nat -> Type
X' n = Vect n Bool

h : (arr (DepAdt TypeCat)) (MkGrothObj Nat X') (MkGrothObj Nat X')
h = MkGrothMor id lm
  where lm : (0 x : Nat) -> X' x -> X' x
        lm _ = map not
