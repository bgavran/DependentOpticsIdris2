module Optics

import Cats
import Groth
import Erased
import DepAct
import WeightedCopara
import Misc

import Data.Either

OpticCat : (c, d, m : Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d m)
  -> Cat
OpticCat c d m l r = WeightedCoparaCat
  (Adt c d)
  (Adt m m)
  (TwoActionsToAdtAction c d m m l r)
  (\mm => m.arr (mm.baseObj) (mm.fibObj))

DepOpticCat : (a : NonDepAct DepAdt DepAdt) -> Cat
DepOpticCat a = WeightedCoparaCat
  DepAdt
  DepAdt
  a
  (\mm => Section (mm.baseObj) (\x => mm.fibObj x))

--OpticToDepOptic : (c, d, m : Cat)
--  -> (l : NonDepAct c m)
--  -> (r : NonDepAct d m)
--  -> OpticCat c d m l r -> DepOpticCat


CoCartOptic : Cat
CoCartOptic = OpticCat TypeCat TypeCat TypeCat CoCartAction CoCartAction

CartOptic : Cat
CartOptic = OpticCat TypeCat TypeCat TypeCat CartAction CartAction

Grate : Cat
Grate = OpticCat TypeCat TypeCat TypeCat HomAction CartAction

AffTraversal : Cat
AffTraversal = OpticCat TypeCat TypeCat (productCat TypeCat TypeCat)  AffTraversalAct AffTraversalAct

-- ArbHom : {A, B : AdtObj}
--   -> (arr CartOptic) A B
--   -> Type
-- ArbHom (MkWCoparaMor (MkGrothObj ?mm ?oo) ?s (MkGrothMor ?ff ?bb)) = ?ee


LensToCartOptic : {A, B : AdtObj}
  -> (arr Lens) (AdtObjToConstCont A) (AdtObjToConstCont B)
  -> (arr CartOptic) A B
LensToCartOptic {A=a} (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj a.baseObj)
  id
  $ MkGrothMor
    (graph f)
    (f' . swap)



LensToClosedForm : {A, B : AdtObj}
  -> (arr Lens) (AdtObjToConstCont A) (AdtObjToConstCont B)
  -> (arr CartOptic) A B
LensToClosedForm {A=a} {B=b} (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj (b.fibObj -> a.fibObj))
  (curry f')
  $ MkGrothMor
  (graph f)
  (\x => (snd x) (fst x))

DepLensToDepOptic : {A, B : Cont0}
  -> (arr DepLens) (Cont0ToCont A) (Cont0ToCont B)
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepLensToDepOptic {A=a} (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj (Unerase a.baseObj))
  (\a => MkUnerase a Refl)
  $ MkGrothMor
    (graph f)
    (\0 _ => lm)
    where lm : (B .fibObj (f a0), Unerase (a .baseObj) a0) -> a .fibObj a0
          lm (b', MkUnerase aRes p) = rewrite p in f' aRes (rewrite (sym p) in b')

DepLensToClosedForm : {A, B : Cont0}
  -> (arr DepLens) (Cont0ToCont A) (Cont0ToCont B)
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepLensToClosedForm {A=a} {B=b} (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj (\0 a0 => b.fibObj (f a0) -> a.fibObj a0))
  f'
  $ MkGrothMor
  (graph f)
  (\0 a0, x => (snd x) (fst x))

DepAdtToDepOptic : {A, B : Cont0}
  -> (arr DepAdt) A B
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepAdtToDepOptic {A=a} (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj () (\0 _ => ()))
  id
  $ MkGrothMor
  (\a => (f a, ()))
  (\0 a0, x => f' a0 (fst x))

record Prism (a, a', b, b' : Type) where
  constructor MkPrism
  build : (b' -> a')
  match : (a -> Either b a')

record PrismL (a, a', b, b' : Type) where
  constructor MkPrismL
  fn : a -> Either (b' -> a') a'

to : Prism a a' b b' -> PrismL a a' b b'
to (MkPrism b m) = MkPrismL (mapFst (const b) . m)
--to (MkPrism b m) = MkPrismL (\a => case m a of
--                                   (Left _) => Left b
--                                   (Right aa) => Right aa)

toGroth : {a, a', b, b' : _} -> Prism a a' b b' -> (arr CoCartOptic) (MkGrothObj a a') (MkGrothObj b b')
toGroth (MkPrism build match) = MkWCoparaMor
  (MkGrothObj a' a')
  id
  (MkGrothMor match (fromEither . mapFst build)) -- (build . fromEither))
-- toGroth (MkPrism build match) = MkDepCoparaMor (MkGrothObj b' a' ** build) (MkGrothMor ?sss ?aaa )

leftPrism1 : Prism Int Int Unit Nat
leftPrism1 = MkPrism
  (fromInteger . cast)
  (\x => if x < 0 then Left () else Right (cast x))

leftPrism : {a, b, c : _} -> (arr CoCartOptic) (MkGrothObj (Either a c) (Either b c)) (MkGrothObj a b)
leftPrism = MkWCoparaMor (MkGrothObj c c) id (MkGrothMor id id)

PrismToDepPrism : {A, B : AdtObj}
  -> (arr CoCartOptic) A B
  -> (arr (DepOpticCat CoCartDepAdt)) (AdtObjToCont0 A) (AdtObjToCont0 B)
PrismToDepPrism (MkWCoparaMor (MkGrothObj rbase rfib) s (MkGrothMor fwd bwd)) = MkWCoparaMor
  (MkGrothObj rbase (\0 _ => rfib))
  s
  $ MkGrothMor
    fwd
    wc
    where wc : (0 a0 : A .baseObj) -> Either0 (fwd a0) (\0 _ => B .fibObj) (\0 _ => rfib) -> A .fibObj
          wc a0 x with 0 (fwd a0)
            wc a0 x | with_pat with (x)
              wc a0 x | (Left x') | (IsLeft y) = bwd (Left y)
              wc a0 x | (Right x') | (IsRight y) = bwd (Right y)

