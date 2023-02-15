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

public export
DepActReparam : (c : Cat)
  -> (f, g : IndCat c)
  -> (r : IndFunctor c g f)
  -> DepAct c f
  -> DepAct c g
DepActReparam c f g r (MkDepAct a) = MkDepAct $ \x => ((a x) . (r x))

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

-- probably don't need the full IndCat here
-- public export
-- adtIndCat : (c, d : Cat)
--   -> (f : IndCat c)
--   -> (g : IndCat (opCat d))
--   -> IndCat (Adt c d)
-- adtIndCat c d f g = MkIndCat
--   (\x => productCat ((mapObj f) (baseObj x)) ((mapObj g) (fibObj x)))
--   (\l, y => (((mapMor f) (baseMor l)) (fst y), ((mapMor g) (fibMor l)) (snd y)))

-- need tensor of two actions
public export
TwoActionsToAdtAction : (c, d, m, n: Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d n)
  -> NonDepAct (Adt c d) (Adt m n)
TwoActionsToAdtAction c d m n l r = MkDepAct (\x, mm => MkGrothObj ((act l) (baseObj x) (baseObj mm)) ((act r) (fibObj x) (fibObj mm)))


public export
CoCartAdt : NonDepAct (Adt TypeCat TypeCat) (Adt TypeCat TypeCat)
CoCartAdt = MkDepAct $ \(MkGrothObj a a'), (MkGrothObj b b') => MkGrothObj
  (Either a b)
  (Either a' b')


public export
CoCartDepAdt : NonDepAct DepAdt DepAdt
CoCartDepAdt = MkDepAct $ \a, b => MkGrothObj
  (Either (a.baseObj) (b.baseObj))
  (\x => Either0 x (a.fibObj) (b.fibObj))

public export
AffTraversalAct : NonDepAct TypeCat (productCat TypeCat TypeCat)
AffTraversalAct = MkDepAct $ \x, mn => Either (fst mn) (Pair (snd mn) x)

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
