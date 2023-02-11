module Cats.DepAct

import Data.DPair
import Data.Either

import Cats.Cats
import Cats.Groth
import Cats.Erased

-- A dependent action on a category `c` is an indexed category over `c`
-- with an action of the fibres on their base.
public export
record DepAct (c : Cat) (bund : IndCat c) where
  constructor MkDepAct
  act : (x : c.obj) -> Functor (bund.mapObj x) c
  -- Equivalently a functor from the Grothendieck construction of bund to c

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Some types of actions
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
NonDepAct : (c, m : Cat) -> Type
NonDepAct c m = DepAct c (constCat m)

public export
FamIndAction : Type
FamIndAction = DepAct TypeCat FamInd
-- includes DPair, Pi

public export
Fam0IndAction : Type
Fam0IndAction = DepAct TypeCat Fam0Ind
-- includes Exists0

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Some embeddings. Important for things to resolve in the typechecker
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- better name? Going to number them
public export
NonDepAct2DepAct : NonDepAct c m -> DepAct c (constCat m)
NonDepAct2DepAct = id

-- better name also
-- public export
-- e2 : FamIndAction -> DepAct TypeCat FamInd
-- e2 = id

-- better name also
-- public export
-- e3 : FamIndAction -> DepAct TypeCat FamInd
-- e3 = id

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Some concrete TypeCat actions
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
CartAction : NonDepAct TypeCat TypeCat
CartAction = MkDepAct Pair

public export
CoCartAction : DepAct TypeCat (constCat TypeCat)
CoCartAction = MkDepAct Either

public export
HomAction : DepAct TypeCat (constCat TypeCat)
HomAction = MkDepAct (\a, b => a -> b)

public export
Proj2Action : DepAct TypeCat (constCat TypeCat)
Proj2Action = MkDepAct (\_ => id)

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Some other concrete actions
--%%%%%%%%%%%%%%%%%%%%%%%%%--


public export
CoCartDepAdt : NonDepAct DepAdt DepAdt
CoCartDepAdt = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => MkGrothObj
  (Either a b)
  (\x => ?bb)
  --(Either a b)
  --(Either a' b')

public export
CoCartAdt : NonDepAct (Adt TypeCat TypeCat) (Adt TypeCat TypeCat)
CoCartAdt = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => MkGrothObj
  (Either a b)
  (Either a' b')

public export
AffTraversalAct : NonDepAct TypeCat (productCat TypeCat TypeCat)
AffTraversalAct = MkDepAct $ \x, (m, n) => Either m (Pair n x)

public export
DepCartAction : FamIndAction
DepCartAction = MkDepAct DPair

public export
DepPiAction : FamIndAction
DepPiAction = MkDepAct (\x, f => (a : x) -> f a)

public export
fibreFamAct : NonDepAct TypeCat TypeCat -> NonDepAct (FamCat a) TypeCat
fibreFamAct f = MkDepAct (\p, b => \a0 => (act f) b (p a0))

public export
fibreFamAct' : NonDepAct TypeCat TypeCat -> NonDepAct (FamCat a) (FamCat a)
fibreFamAct' f = MkDepAct (\p, b => \a => (act f) (b a) (p a))

public export
DepCart0Action : Fam0IndAction
DepCart0Action = MkDepAct Exists0


-- Every monoidal product on Set gives rise to a monoidal product on DepLens
-- This is given pointwise, see https://arxiv.org/abs/2202.00534
public export
DepLensNonDepAct : NonDepAct TypeCat TypeCat -> NonDepAct DepLens DepLens
DepLensNonDepAct (MkDepAct ac) = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => (MkGrothObj
  (Pair a b)
  (\x => ac (a' (fst x)) (b' (snd x))))


-- Works for dependent adapters too
public export
DepAdtNonDepAct : NonDepAct TypeCat TypeCat -> NonDepAct DepAdt DepAdt
DepAdtNonDepAct ac = MkDepAct $ \aa', bb' => (MkGrothObj
  (Pair aa'.baseObj bb'.baseObj)
  (\x => (act ac) (aa'.fibObj (fst x)) (bb'.fibObj (snd x))))


-- Works for adapters too... but this uses the same action on both places?
public export
AdtNonDepAct : NonDepAct TypeCat TypeCat -> NonDepAct (Adt TypeCat TypeCat) (Adt TypeCat TypeCat)
AdtNonDepAct (MkDepAct ac) = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => (MkGrothObj
  (Pair a b)
  (ac a' b'))
  -- (\x => ac (a' (fst x)) (b' (snd x))))


-- Works for bimorphic lenses too
public export
LensNonDepAct : NonDepAct TypeCat TypeCat -> NonDepAct Lens Lens
LensNonDepAct (MkDepAct ac) = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => (MkGrothObj
  (Pair a b)
  (ac a' b'))

-- -- What about dependent adapters being acted on by dependent lenses?
-- DepAdtNonDepActL : NonDepAct TypeCat TypeCat -> NonDepAct DepAdt DepLens
-- DepAdtNonDepActL (MkDepAct ac) = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => (MkGrothObj
--   (Pair a b)
--   (\x => ac (a' (fst x)) (b' (?bb))))


----

-- Data we need to specify the action per fiber
public export
record OverDepAct (c : Cat) (bund : IndCat c) (action : DepAct c bund) (d : IndCat c) where
  constructor MkOverDepAct
  actt : (y : obj c) -- an output y:C
      -> (m : obj (bund.mapObj y)) -- something over y that acts on it
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
CospanOverAct : OverDepAct TypeCat FamInd DepCartAction FamInd
CospanOverAct = MkOverDepAct (\y, m, yy', dpl => Exists m) -- (. fst))
-- CospanOverAct = MkOverDepAct (\y, _, yy', dpl => yy' (fst dpl))
  -- (\y, m => mapMor FamInd fst)

public export
Cospan0OverAct : OverDepAct TypeCat Fam0Ind DepCart0Action Fam0Ind
Cospan0OverAct = MkOverDepAct (\y, m, y', dp => (y' (fst dp), m (fst dp))) -- (y' (fst dp), m (fst dp))) --  --(m, f (fst g)))

-- "Whatever is over y is going to also be over (y, y'), for any y'"
-- Given two indexed categories d and bnd over c, it creates an indexed category over FLens c d using only bnd (ignoring d)
public export
ExtendIndCat : (c : Cat)
  -> (d : IndCat c) -- Fam0Ind
  -> (bnd : IndCat c) -- action, plus
  -> IndCat (FLens c d)
ExtendIndCat _ _ bnd = MkIndCat (bnd.mapObj . baseObj) (bnd.mapMor . baseMor)

public export
CartDOpticAct : (d : IndCat TypeCat) -> Type
CartDOpticAct d = DepAct (FLens TypeCat Fam0Ind) (ExtendIndCat TypeCat Fam0Ind d)

-- public export
-- e4 : CartDOpticAct d -> DepAct (FLens TypeCat Fam0Ind) (ExtendIndCat TypeCat Fam0Ind d)
-- e4 = id
