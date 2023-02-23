module Cats.Optics

import Cats.Cats
import Cats.Groth
import Cats.Erased
import Cats.DepAct
import Cats.DepCoPara
import Cats.Misc

import Data.Either

-- Tw(M) acts on Adapters!!!
-- action induced by reparameterisation along tw(M) -> MxM^op
OpticAct : (c : Cat)
  -> (d : Cat)
  -> (m : Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d m)
  -> NonDepAct (Adt c d) (TwistedArr m)
OpticAct c d m l r = DepActReparam
  (Adt c d)
  (constCat (Adt m m))
  (constCat (TwistedArr m))
  (\_ => TwistedArrProj m) $ TwoActionsToAdtAction c d m m l r
-- the implementation above essentially does this:
--MkDepAct $ \xx', (m ** _) =>
--  (MkGrothObj ((act l) xx'.baseObj m.baseObj) ((act r) xx'.fibObj m.fibObj))

DepOpticAct : (a : NonDepAct DepAdt DepAdt)
  -> NonDepAct DepAdt Dep0TwistedArr
DepOpticAct a = DepActReparam
  DepAdt
  (constCat DepAdt)
  (constCat (Dep0TwistedArr))
  (\_ => Dep0TwistedArrProj)
  a
--MkDepAct $ \xx', (m ** _) => (act a) xx' m

DepOpticCat : (a : NonDepAct DepAdt DepAdt)
  -> Cat
DepOpticCat a = DepCoparaCat DepAdt (constCat Dep0TwistedArr) (DepOpticAct a)

OpticCat : (c : Cat)
  -> (d : Cat)
  -> (m : Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d m)
  -> Cat
OpticCat c d m l r = DepCoparaCat (Adt c d) (constCat (TwistedArr m)) (OpticAct c d m l r)

CoCartOptic : Cat
CoCartOptic = OpticCat TypeCat TypeCat TypeCat CoCartAction CoCartAction

CartOptic : Cat
CartOptic = OpticCat TypeCat TypeCat TypeCat CartAction CartAction

Grate : Cat
Grate = OpticCat TypeCat TypeCat TypeCat HomAction CartAction

AffTraversal : Cat
AffTraversal = OpticCat TypeCat TypeCat (productCat TypeCat TypeCat)  AffTraversalAct AffTraversalAct

-- ArbHom : {A, B : AdtObj}
--   -> (arr AffTraversal) A B
--   -> Type
-- ArbHom (MkDepCoparaMor (MkGrothObj m n ** s) (MkGrothMor f b)) = ?ee

LensToCartOptic : {A, B : AdtObj}
  -> (arr Lens) (AdtObjToConstCont A) (AdtObjToConstCont B)
  -> (arr CartOptic) A B
LensToCartOptic {A=a} (MkGrothMor f f') = MkDepCoparaMor
  (MkGrothObj a.baseObj a.baseObj ** id)
  $ MkGrothMor
    (graph f)
    (f' . swap)

--
LensToClosedForm : {A, B : AdtObj}
  -> (arr Lens) (AdtObjToConstCont A) (AdtObjToConstCont B)
  -> (arr CartOptic) A B
LensToClosedForm {A=a} {B=b} (MkGrothMor f f') = MkDepCoparaMor
  (MkGrothObj a.baseObj (b.fibObj -> a.fibObj) ** (curry f'))
  $ MkGrothMor
    (graph f)
    (\x => (snd x) (fst x))


DepLensToDepOptic : {A, B : Cont0}
  -> (arr DepLens) (Cont0ToCont A) (Cont0ToCont B)
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepLensToDepOptic {A=a} (MkGrothMor f f') = MkDepCoparaMor
  (MkGrothObj a.baseObj (Unerase a.baseObj) ** (\a => MkUnerase a Refl))
  $ MkGrothMor
    (graph f)
    (\0 _ => lm) -- without the where clause Idris complains
    where lm : (B .fibObj (f a0), Unerase (a .baseObj) a0) -> a .fibObj a0
          lm (b', MkUnerase aRes p) = rewrite p in f' aRes (rewrite (sym p) in b')


DepLensToClosedForm : {A, B : Cont0}
  -> (arr DepLens) (Cont0ToCont A) (Cont0ToCont B)
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepLensToClosedForm {A=a} {B=b} (MkGrothMor f f') = MkDepCoparaMor
  (MkGrothObj a.baseObj (\0 a0 => b.fibObj (f a0) -> a.fibObj a0) ** f')
  $ MkGrothMor
    (graph f)
    (\0 a0, x => (snd x) (fst x))

DepAdtToDepOptic : {A, B : Cont0}
  -> (arr DepAdt) A B
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepAdtToDepOptic {A=a} (MkGrothMor f f') = MkDepCoparaMor
  ((MkGrothObj () (\0 _ => ())) ** id)
  $ MkGrothMor
    (\a => (f a, ()))
    (\0 a0, x => f' a0 (fst x))

record Prism (a, a', b, b' : Type) where
  constructor MkPrism
  build : (b' -> a')
  match : (a -> Either b a')


record DPrism1 (a : Type) (a' : (0 _ : a) -> Type)
               (b : Type) (b' : (0 _ : b) -> Type) where
  constructor MkDPrism1
  res : Type
  res' : (0 _ : res) -> Type
  resMap : (r : res) -> res' r
  match : a -> Either b res
  build : (0 x : a) ->
          Either0 (match x) b' res' -> a' x

DPrism1ToGroth : DPrism1 a a' b b' ->
  (arr (DepOpticCat CoCartDepAdt))
    (MkGrothObj a a')
    (MkGrothObj b b')
DPrism1ToGroth (MkDPrism1 r r' rm m b) = MkDepCoparaMor
  (MkGrothObj r r' ** rm)
  (MkGrothMor m b)

PrismGroth : (a : Type) -> (a' : (0 _ : a) -> Type) ->
             (b : Type) -> (b' : (0 _ : b) -> Type) ->
             Type
PrismGroth a a' b b' =
  (arr (DepOpticCat CoCartDepAdt)) (MkGrothObj a a') (MkGrothObj b b')

toGroth : {a, a', b, b' : _} -> Prism a a' b b' ->
  (arr CoCartOptic) (MkGrothObj a a') (MkGrothObj b b')
toGroth (MkPrism build match) = MkDepCoparaMor
  (MkGrothObj a' a' ** id)
  (MkGrothMor match (fromEither . mapFst build))

natPrism : Prism Int Int Unit Nat
natPrism = MkPrism
  (fromInteger . cast)
  (\x => if x < 0 then Left () else Right (cast x))

Prism' : Type -> Type -> Type
Prism' a b = Prism a a b b

maybePrism : Prism (Maybe a) (Maybe a) a a
maybePrism = MkPrism Just (maybe (Right Nothing) Left)

data IsJust : (0 _ : Maybe a) -> Type where
  ItIsJust : (x : a) -> IsJust (Just x)

isItJust : (x : Maybe a) -> Dec (IsJust x)

maybeDPrism : {a : _} -> DPrism1 (Maybe a) (\_ => Maybe a) a (\_ => a)
maybeDPrism = MkDPrism1
  Unit
  (\x => Unit)
  id
  (maybe (Right ()) Left)
  (\0 x', k => elimEither0' {m = \k => Maybe a } _ (\_ => Just) (\_, _ => Nothing) k)

maybeDPrism' : {a : _} -> DPrism1 (Maybe a) (\_ => Maybe a) a (\_ => a)
maybeDPrism' = MkDPrism1
  (Maybe a)
  (\x => IsJust x)
  ?www
  (\x => ?Left)
  ?bb
  -- (maybe (Right ()) Left)
  -- (\0 x', k => elimEither0' {m = \k => Maybe a } _ (\_ => Just) (\v, v' => ?ww) k)

  {-

leftPrism : Prism (Either a b) (Either a b) a a
leftPrism = MkPrism
  Left
  (either Left (Right . Right))

PrismToDepPrism : {A, B : AdtObj}
  -> (arr CoCartOptic) A B
  -> (arr (DepOpticCat CoCartDepAdt)) (AdtObjToCont0 A) (AdtObjToCont0 B)
PrismToDepPrism (MkDepCoparaMor (MkGrothObj rbase rfib ** s) (MkGrothMor fwd bwd)) = MkDepCoparaMor
  (MkGrothObj rbase (\0 _ => rfib) ** s)
  $ MkGrothMor
    fwd
    (\0 x, e => elimEither0 {m = \_ => fibObj A} _ (\_ => bwd . Left) (\_ => bwd . Right) e)

data IsEven : (0 _ : Nat) -> Type where
  ZeroEven : IsEven Z
  SuccSuccEven : IsEven n -> IsEven (S (S n))

data IsOdd : (0 _ : Nat) -> Type where
  OneOdd : IsOdd 1
  SuccSuccOdd : IsOdd n -> IsOdd (S (S n))

dependent_match : (n : Nat) -> IsEven n -> (IsOdd (S n))
dependent_match 0 ZeroEven = (OneOdd)
dependent_match (S (S n)) (SuccSuccEven x) =
  let v = dependent_match n x in
      (SuccSuccOdd (v))

test : dependent_match 4 %search = SuccSuccOdd (SuccSuccOdd OneOdd)
test = Refl

isOdd : (x : Nat) -> Dec (IsOdd x)
isOdd 0 = No (\case _ impossible)
isOdd (S 0) = Yes OneOdd
isOdd (S (S k)) = case isOdd k of
                       Yes p => Yes (SuccSuccOdd p)
                       No c => No (\case (SuccSuccOdd x) => c x)

evenPrism : DPrism1 Nat (\0 n => Nat) Nat IsEven
evenPrism = MkDPrism1
  Nat
  (\x => Dec (IsOdd x))
  --(\x => Subset0 Nat (\y => (IsOdd y, y === x)))
  isOdd
  isEven
  (\0 k => elimEither0 {m = \_ => Nat} (isEven k) ?aa ?mmm)
  --(\0 x, e => elimEither0 {m = ty x} (isEven x) ?aaa ?dd e)
  where
    ty : Nat -> Either0 e IsEven (\0 n => Nat) ->  Type
    ty x _ = IsOdd (S x)-- elimEither0 {m = \_ => Type} e ?aa ?bb

    isEven : Nat -> Either Nat Nat
    isEven 0 = Left 0
    isEven (S n) = Right n

    even2Odd : (0 y : Nat) -> IsEven y -> IsOdd (S y)
    even2Odd 0 ZeroEven = OneOdd
    even2Odd (S (S n)) (SuccSuccEven y) = SuccSuccOdd (even2Odd n y)



