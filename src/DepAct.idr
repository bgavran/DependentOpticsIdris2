module DepAct

import Data.DPair
import Data.Either

import Cats
import Groth
import Erased

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
DepActReparam c f g r (MkDepAct a) = MkDepAct $ \x => MkFunctor
  ((a x).mapObj . (r x).mapObj)
  (\_, _ => (a x).mapMor _ _ . (r x).mapMor _ _)

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Some types of actions
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
NonDepAct : (c, m : Cat) -> Type
NonDepAct c m = DepAct c (constCat m)

public export
FamIndAction : Type
FamIndAction = DepAct TypeCat (FamInd TypeCat)
-- includes DPair, Pi

public export
Fam0IndAction : Type
Fam0IndAction = DepAct TypeCat (Fam0Ind TypeCat)
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
CartAction = MkDepAct $ \x => MkFunctor (Pair x) (\_, _ => mapSnd)

public export
CoCartAction : DepAct TypeCat (constCat TypeCat)
CoCartAction = MkDepAct $ \x => MkFunctor (Either x) (\_, _ => mapSnd)

public export
HomAction : DepAct TypeCat (constCat TypeCat)
HomAction = MkDepAct $ \a => MkFunctor (\b => a -> b) (\_, _ => (.))

public export
Proj2Action : DepAct TypeCat (constCat TypeCat)
Proj2Action = MkDepAct $ \_ => idFunctor _

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
TwoActionsToAdtAction c d m n l r = MkDepAct $ \x => MkFunctor
  (\mm => MkGrothObj (((act l) (baseObj x)).mapObj (baseObj mm)) (((act r) (fibObj x)).mapObj (fibObj mm)))
  (\_, _, mm => MkGrothMor (((act l) (baseObj x)).mapMor _ _ (baseMor mm)) (((act r) (fibObj x)).mapMor _ _ (fibMor mm)))


-- )

public export
CoCartAdt : NonDepAct (Adt TypeCat TypeCat) (Adt TypeCat TypeCat)
CoCartAdt = MkDepAct $ \a => MkFunctor
  (\b => MkGrothObj (Either a.baseObj b.baseObj) (Either a.fibObj b.fibObj))
  (\_, _, f => MkGrothMor (mapSnd f.baseMor) (mapSnd f.fibMor))



public export
CoCartDepAdt : NonDepAct (DepAdt TypeCat) (DepAdt TypeCat)
CoCartDepAdt = MkDepAct $ \a => MkFunctor
  (\b => MkGrothObj (Either (a.baseObj) (b.baseObj)) (\x => EitherCheck x (a.fibObj) (b.fibObj)))
  (\x, y, f => MkGrothMor (mapSnd f.baseMor)
      (\x0 => \case (IsLeft' {x=h} val check) =>
                      let (v' ** (p1, p2)) = bimapLeft x0 h check
                      in IsLeft' val (p1 `trans` cong Left p2)
                    (IsRight' {x=h} val check) =>
                      let (v' ** (p1, p2)) = bimapRight x0 h check
                      in IsRight' (f.fibMor v' (replace {p = y.fibObj} (sym p2) val)) p1))


public export
AffTraversalAct : NonDepAct TypeCat (productCat TypeCat TypeCat)
AffTraversalAct = MkDepAct $ \x => MkFunctor
  (\mn => Either (fst mn) (Pair (snd mn) x))
  (\_, _, mn => bimap (fst mn) (mapFst (snd mn)))

public export
DepCartAction : FamIndAction
DepCartAction = MkDepAct $ \x => MkFunctor
  (DPair x)
  (\_, _, f, dp => (fst dp ** f (fst dp) (snd dp))) -- mapSnd instance for DPair?

-- public export
-- DepPiAction : FamIndAction
-- DepPiAction = MkDepAct $ \x => MkFunctor
--   (\f => (a : x) -> f a)
--   (\f, g, a => f a ?ef) -- f => (a : x) -> f a)

{-
public export
DepCart0Action : Fam0IndAction
DepCart0Action = MkDepAct DPair -- Exists0
-}

0 objProd : NonDepAct TypeCat TypeCat
  -> (a, b : Cont)
  -> Cont
objProd ac a b = MkGrothObj
  (Pair a.baseObj b.baseObj)
  (\x => ((act ac) (a.fibObj (fst x))).mapObj (b.fibObj (snd x)))

-- Every monoidal product on Set gives rise to a monoidal product on DepLens
-- This is given pointwise, see https://arxiv.org/abs/2202.00534
public export
FromActionOnBaseDepLens : NonDepAct TypeCat TypeCat -> NonDepAct (DepLens TypeCat) (DepLens TypeCat)
FromActionOnBaseDepLens ac = MkDepAct $ \a => MkFunctor
  (objProd ac a)
  (\_, _, f => MkGrothMor
      (mapSnd f.baseMor)
      (\(aLeft, xRight) => ((act ac) (a.fibObj aLeft)).mapMor _ _ ((f.fibMor) xRight)))

-- Works for dependent adapters too
public export
FromActionOnBase : NonDepAct TypeCat TypeCat -> NonDepAct (DepAdt TypeCat) (DepAdt TypeCat)
FromActionOnBase ac = MkDepAct $ \aa' => MkFunctor
  (\bb' => MkGrothObj (Pair aa'.baseObj bb'.baseObj) (\x => ((act ac) (aa'.fibObj (fst x))).mapObj (bb'.fibObj (snd x))))
  (\_, _, f => MkGrothMor
      (mapSnd f.baseMor)
      (\(aLeft, xRight) => (((act ac) (aa'.fibObj aLeft)).mapMor _ _ ((f.fibMor) xRight))))

  {-

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
