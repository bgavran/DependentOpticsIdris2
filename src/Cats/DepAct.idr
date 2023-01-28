module Cats.DepAct

import Cats.Cats
import Cats.Groth
import Cats.Erased

-- A dependent action on a category `c` is an indexed category over `c`
-- with an action of the fibres on their base.
public export
record DepAct (c : Cat) where
  constructor MkDepAct
  bund : IndCat c
  act : (x : c.obj) -> Functor (bund.mapObj x) c
  -- we can uncurry this to become a functor from Groth construction to c

-- public export
-- record DepAct2 (c : Cat) where
--   constructor MkDepAct2
--   bund2 : IndCat c
--   act2 : (a : c.obj) -> Functor (bund2.mapObj a) c

public export
CartAction : DepAct TypeCat
CartAction = MkDepAct
  (MkIndCat (\_ => TypeCat) (\_ => id))
  (,)


public export
DepCartAction : DepAct TypeCat
DepCartAction = MkDepAct FamInd DPair

public export
DepCart0Action : DepAct TypeCat
DepCart0Action = MkDepAct Fam0Ind Exists0


-- Data we need to specify the action per fiber
public export
record OverDepAct (c : Cat) (action : DepAct c) (d : IndCat c) where
  constructor MkOverDepAct
  actt : (0 y : obj c) -- an output y:C
      -> (m : obj (action.bund.mapObj y)) -- something over y that acts on it
      -> (y' : obj ((fibOp c d).mapObj y)) -- something over y
      ->       obj ((fibOp c d).mapObj (action.act y m)) -- something over m * y

-- Combine two X-indexed sets into one indexed sets
-- FamInd appears twice, once in DepCartAction and once here in type
-- Indexed by the dependent pair, but functionally doesn't depend on it
i : (0 y : Type) -- You get a set Y
  -> (m : y -> Type) -> (y' : (0 _ : y) -> Type) -- You get 2 Y-indexed sets
  -> (0 _ : (y0 : y ** m y0)) -> Type -- Create a (y0 : y ** m y0)-indexed Set
i _ _ y' = \dp => y' (fst dp) -- by only indexing over y0 using y'
-- i y m = (mapMor FamInd) fst -- by only indexing over y0 using y'

public export
CospanOverAct : OverDepAct TypeCat DepCartAction FamInd
CospanOverAct = MkOverDepAct (\y, _ => (. fst))
-- CospanOverAct = MkOverDepAct (\y, _, yy', dpl => yy' (fst dpl))
  -- (\y, m => mapMor FamInd fst)

public export
Cospan0OverAct : OverDepAct TypeCat CartAction Fam0Ind
Cospan0OverAct = MkOverDepAct (\_, m, f, g => (m, f (fst g)))

-- project out first element
-- Whatever is over y is going to also be over (y, y'), for any y'
-- not used in function below because idris then doesn't reduce
ExtendIndCat : (c : Cat) -> (d : IndCat c) -> (m : IndCat c) -> IndCat (FLens c d)
ExtendIndCat c d m = MkIndCat (m.mapObj . baseObj) (m.mapMor . baseMor)

-- drops the base, FamInd is here two times
-- FamInd is inside DepAct
public export
-- TODO refactor this
GrothAct : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c)
          -> OverDepAct c m d
          -> DepAct (FLens c d)
GrothAct c m d doa = MkDepAct
  -- what this says is that the things that can act on (x, x') in D^ are exactly the
  -- things that can act on x in C (where C <-- D^)
  -- (MkIndCat ?zii ?zij)
  (MkIndCat (m.bund.mapObj . baseObj) (m.bund.mapMor . baseMor))
  -- (ExtendIndCat c d m.bund)
  -- ^ doubly indexed category (i.e. indexed over the total space)
  (\grrr, m' => MkGrothObj (m.act (baseObj grrr) m') (doa.actt (baseObj grrr) m' (fibObj grrr)))
  -- (\(MkGrothObj xbase xpoint), m' => MkGrothObj (m.act xbase m') (doa.actt xbase m' xpoint))
  --(\(MkGrothObj gr grr), m' => (MkGrothObj (m.act gr m') ?el))
