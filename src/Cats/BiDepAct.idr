module Cats.BiDepAct

{-
%%%%%%%%%%
Mostly an experimental place where possible categorical semantics of copara maps like
res : A -> Type
f : (a : A) -> M B (res a)
are explored.
%%%%%%%%%%
-}

import Cats.Cats
import Cats.Groth
import Cats.Erased
import Cats.DepAct

public export
record FiberwiseDepAct (c : Cat) (d : IndCat c) where
  constructor MkFiberwiseDepAct
  reindex : {0 a : c.obj} -> NonDepAct (d.mapObj a) c
                     -- -> (b : c.obj) -> Functor (d.mapObj a) (d.mapObj a)

{-
Takes the action of p (because it's usually the pi-type) on a (which gives us a Functor (d.mapObj a) -> c), and acts on it by first using b to map from (d.mapObj a) to (d.mapObj a), and *then* acting.
-}
public export
biact : (c : Cat)
  -> (d : IndCat c)
  -> (p : DepAct c d) -- This is essentially Pi type
  -> (r : FiberwiseDepAct c d)
  -> (a, b : c.obj)
  -> Functor (d.mapObj a) c
biact _ d p r a b = \res => (((act p) a) (act (reindex r) res b))


public export
FamReindex : (f : NonDepAct TypeCat TypeCat)
  -> FiberwiseDepAct TypeCat FamInd
FamReindex f = MkFiberwiseDepAct (fibreFamAct f)
-- we ignore the first argument above because over every object we do the same thing

constCatReindex : (f : NonDepAct c c)
  -> FiberwiseDepAct c (constCat c)
constCatReindex f = MkFiberwiseDepAct (MkDepAct (flip (act f)))

-- works only for TypeCat
record DoubleDepCoparaMor
  (d : IndCat TypeCat)
  (p : DepAct TypeCat d)
  (r : FiberwiseDepAct TypeCat d)
  (A, B : Type) where
  constructor MkDDCoparaMor
  res : (d.mapObj A).obj
  fwPara : biact TypeCat d p r A B res

public export
BiDepCoparaCat : (d : IndCat TypeCat)
  -> (f : DepAct TypeCat d)
  -> (r : FiberwiseDepAct TypeCat d)
  -> Cat
BiDepCoparaCat d f r = MkCat Type (DoubleDepCoparaMor d f r)

public export
record DepOptic
  -- (d : IndCat TypeCat) -- This seems to only work for FamInd
  (r : FiberwiseDepAct TypeCat FamInd)
  (A, B : Type)
  (A' : A -> Type)
  (B' : B -> Type) where
  constructor MkDepOptic
  fw : (arr (BiDepCoparaCat FamInd DepPiAction r) A B)
  bw : (0 a : A)
    -- -> (g : (fwPara fw) a)  -- (act (reindex r)) (res a) B ---> (act (reindex r)) (res a) (0 b : B ** B' b)
    -- -> (r : (res fw) a)
    -- -> (res fw) a
    -- -> B' (fwPara fw)
    -> A' a
  -- bw : (0 a : shp A)
  -- -> (res1 fw) a -- something over a that acts on it
  -- -> pos B (fst ((fw1 fw) a)) -- something over f a
  -- -> pos A a -- something over a

{-
CoparaMor : {C : Type}
  -- (arr (BiDepCoparaCat (constCat TypeCat) HomAction (constCatReindex CartAction))) Bool C
  -> (arr (BiDepCoparaCat FamInd DepPiAction (FamReindex CoCartAction))) Bool C
CoparaMor = MkDDCoparaMor
  (\b => if b == True then String else Nat)
  (\a => case a of
    True => ?ll
    False => ?bn)
-}

reindexCoparaMor : {b' : b -> Type}
  -> (f : NonDepAct TypeCat TypeCat)
  -> arr (BiDepCoparaCat FamInd DepPiAction (FamReindex f)) a b
  -> arr (BiDepCoparaCat FamInd DepPiAction (FamReindex f)) a (b1 : b ** b' b1)
reindexCoparaMor (MkDepAct ac) (MkDDCoparaMor r f) = MkDDCoparaMor
  r
  (\a => let t = f a in ?em)
{-
-- ?
DOpticMor : (A, B : Type)
  -> (A' : A -> Type)
  -> (B' : B -> Type)
  -> (arr DLens) (MkGrothObj A (A')) (MkGrothObj B (B'))
  -> (arr (BiDepCoparaCat FamInd DepPiAction (FamReindex CoCartAction))) A B
DOpticMor a b a' b' (MkGrothMor f f') = MkDDCoparaMor
  (\a => ?rr)
  ?ff
-}

-- arbitraryReindex : (c : Cat)
--   -> (d : IndCat c)
--   -> (f : NonDepAct c c)
--   -> FiberwiseDepAct c d
-- arbitraryReindex c d (MkDepAct f) = MkFiberwiseDepAct (\a => (MkDepAct (?rr))) -- , b => ?ll)

f : {A, B : Type} -> (A -> Type) -> Type
f = biact TypeCat FamInd DepPiAction (FamReindex CartAction) A B

g : {A, B : Type} -> (Type -> Type)
g = biact TypeCat (constCat TypeCat) HomAction (constCatReindex CartAction) A B

-- g' : {A, B : Type} -> (res : Type) -> g res
-- g' res = ?qwee
