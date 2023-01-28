module Cats.ChurchForRealz

import Data.DPair
import Erased
import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.DepCoPara
import Cats.DepOptics

embedCartLensFLens : (a -> b) -> (a -> b' -> a') -> (arr DLens) (MkGrothObj a (\_ => a')) (MkGrothObj b (\_ => b'))
embedCartLensFLens f f' = MkGrothMor f f'


CartesianOptic : (x, x', y, y' : Type) -> Type
CartesianOptic x x' y y' = DependentOptics TypeCat CartAction
  (MkIndCat (\_ => TypeCat) (\_ => id))
  (MkOverDepAct (\_ => Pair)) x x' y y'

graph : (a -> b) -> (a -> (b, a))
graph f = \a => (f a, a)

embedLensintoDepOptic : (a -> b) -> ((a, b') -> a') -> CartesianOptic a a' b b'
embedLensintoDepOptic f fsharp = MkCoparaMor a (MkGrothMor (graph f) fsharp)

-- objects of Fam(Set) are containers
Cont : Type
Cont = GrothObj TypeCat (fibOp TypeCat FamInd)

Cont0 : Type
Cont0 = GrothObj TypeCat (fibOp TypeCat Fam0Ind)

-- using FamInd twice below!
CartDepOptics : Cat
CartDepOptics = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct

CartDepOptics0 : Cat
CartDepOptics0 = DependentOpticsCat TypeCat CartAction Fam0Ind Cospan0OverAct

record DLens0 (a : Cont0) (b : Cont0) where
  constructor MkDLens0
  fwd : a.baseObj -> b.baseObj
  bck : (x : a.baseObj) -> b.fibObj (fwd x) -> a.fibObj x

record DLens (a : Cont) (b : Cont) where
  constructor MkDLens
  fwd : a.baseObj -> b.baseObj
  bck : (x : a.baseObj) -> b.fibObj (fwd x) -> a.fibObj x

record ClDLens (a : Cont) (b : Cont) where
  constructor MkClDLens
  cl : (x : a.baseObj) -> (y : b.baseObj ** b.fibObj y -> a.fibObj x)

DepGraph : (f : a -> b) -> (a -> (x : b ** a))
DepGraph f a = (f a ** a)

depApt2DepOptic : arr DepAdt a b -> arr CartDepOptics0 a b
depApt2DepOptic (MkGrothMor alonzo church) =
  MkCoparaMor Unit (MkGrothMor (\x => (alonzo x, ())) (\0 z, w => church z (snd w)))

normalLenses2DepOptic : {0 a : Type} -> (a -> b) -> ((a, b') -> a') -> arr CartDepOptics0
   (MkGrothObj a (\_ => a')) (MkGrothObj b (\_ => b'))
normalLenses2DepOptic f g = MkCoparaMor a (MkGrothMor (\x => (f x, x)) (\0 _ => g))

DLenstoDepOptic : (A, B : Cont0) -> DLens0 A B -> (arr CartDepOptics0) A B
DLenstoDepOptic (MkGrothObj a a') (MkGrothObj b b') (MkDLens0 fwd bwd) = MkCoparaMor ?rr ?ff -- a (MkGrothMor (\x => (fwd x, ?rr)) ?bb)
  -- MkCoparaMor a
  -- (MkGrothMor (\x => (fwd x, x)) ?please)
-- f = (\x => a , x == a)
-- (x : a) -> (0 res : f a) -> (b' (fwd x)) -> a' x

-- DLenstoDepOptic (MkGrothObj a a') (MkGrothObj b b') (MkDLens f f') = MkCoparaMor
--   (\_ => a)
--   (MkGrothMor (DepGraph f) ?bwl) -- f')

-- testDepOptic : (arr CartDepOptics) (MkGrothObj String (\s => ())) (MkGrothObj () (\_ => ()))
-- testDepOptic = MkCoparaMor
--   (?tt)
--   (MkGrothMor (\s => (() ** ?l)) ?bw)


{-
ClDLenstoDepOptic : (A, B : Cont) -> ClDLens A B -> (arr CartDepOptics) A B
ClDLenstoDepOptic (MkGrothObj a a') (MkGrothObj b b') (MkClDLens cl)= MkCoparaMor
-- TODO put 0 x here, ask Andre
  (\b => Bool)-- (x : a ** b' b -> a' x)) -- needs to hold (fst cl) x = b
  (MkGrothMor
    ?fw -- (\x => (fst (cl x) ** (x ** snd (cl x))))
    ?bw)

-- because we don't know that fst (cl x) = ?
-- DLenstoDepOptic (MkGrothObj aPos aDir) (MkGrothObj bPos bDir)
        --(\x => a.baseObj)
  --(MkGrothMor
  --  (graph f.fwd)
  --  f.bck)
