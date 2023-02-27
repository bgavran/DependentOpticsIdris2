module Groth

import Cats
import Erased
import Misc

import Data.Vect

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
           ((d.mapMor {x = s.baseObj} {y = t.baseObj} baseMor).mapObj t.fibObj)

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
DepAdt : (d : Cat) -> Cat
DepAdt d = FLens TypeCat (Fam0Ind d)

public export
DepLens : (d : Cat) -> Cat
DepLens d = FLens TypeCat (FamInd d)

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
Cont = GrothObj TypeCat (fibOp TypeCat (FamInd TypeCat))

-- ContAdt is isomorphic to Cont
public export
ContAdt : Type
ContAdt = GrothObj TypeCat (fibOp TypeCat (Fam0Ind TypeCat))

public export
ConstCont : Type
ConstCont = GrothObj TypeCat (fibOp TypeCat CoKleisliInd)

public export
AdtObj : Type
AdtObj = GrothObj TypeCat (fibOp TypeCat (constCat TypeCat))

public export
AdtObjC : (c : Cat) -> Type
AdtObjC c = GrothObj c (fibOp c (constCat c))

-- they're isomorphic
public export
ConstContToAdtObj : ConstCont -> AdtObj
ConstContToAdtObj cc = MkGrothObj cc.baseObj cc.fibObj

-- they're isomorphic
public export
ContToContAdt : Cont -> ContAdt
ContToContAdt c = MkGrothObj c.baseObj c.fibObj

--- %%%% Four kinds of embeddings, actions on morphisms
public export
DepAdtToDepLens : Functor (DepAdt TypeCat) (DepLens TypeCat)
DepAdtToDepLens = MkFunctor
  (\c0 => MkGrothObj c0.baseObj c0.fibObj)
  (\f => MkGrothMor f.baseMor (\a => f.fibMor a))
  -- can't completely eta-reduce because of lack of subtyping of erasable types

public export
LensToDepLens : Functor Lens (DepLens TypeCat)
LensToDepLens = MkFunctor
  (\cc => MkGrothObj cc.baseObj (\ _=> cc.fibObj))
  (\f => MkGrothMor f.baseMor (curry f.fibMor)) -- hmm we need to curry

public export
AdtToLens : Functor (Adt TypeCat TypeCat) Lens
AdtToLens = MkFunctor
  (\ao => MkGrothObj ao.baseObj ao.fibObj)
  (\f => MkGrothMor f.baseMor (f.fibMor . snd)) -- hmm we need to curry

public export
AdtToDepAdt : Functor (Adt TypeCat TypeCat) (DepAdt TypeCat)
AdtToDepAdt = MkFunctor
  (\ao => MkGrothObj ao.baseObj (\_ => ao.fibObj))
  (\f => MkGrothMor f.baseMor (\_ => f.fibMor))

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Hom, DepHom
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
Hom : {m : Cat} -> Functor (Adt m m) (opCat TypeCat)
Hom = MkFunctor (\o => (arr m) o.baseObj o.fibObj) ?zza -- need composition to implement!

public export
DepHom : Functor (DepAdt TypeCat) (opCat TypeCat)
DepHom = MkFunctor (\o => DFunction o.baseObj o.fibObj) ?zzb -- need composition to implement!


--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Testing, example
--%%%%%%%%%%%%%%%%%%%%%%%%%--

X' : Nat -> Type
X' n = Vect n Bool


h : (arr (DepAdt TypeCat)) (MkGrothObj Nat X') (MkGrothObj Nat X')
h = MkGrothMor id lm
  where lm : (0 x : Nat) -> X' x -> X' x
        lm _ = map not
