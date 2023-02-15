module Cats.Optics

import Cats.Cats
import Cats.Groth
import Cats.Erased
import Cats.DepAct
import Cats.DepCoPara
import Cats.Misc

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

dia : Either a a -> a
dia (Left x) = x
dia (Right x) = x

record Prism (a, a', b, b' : Type) where
  constructor MkPrism
  build : (b' -> a')
  match : (a -> Either b a')

record PrismL (a, a', b, b' : Type) where
  constructor MkPrismL
  fn : a -> Either (b' -> a') a'

to : Prism a a' b b' -> PrismL a a' b b'
to (MkPrism b m) = MkPrismL (mapFst (const b) . m )

toGroth : {a, a', b, b' : _} -> Prism a a' b b' -> (arr CoCartOptic) (MkGrothObj a a') (MkGrothObj b b')
toGroth (MkPrism build match) = MkDepCoparaMor (MkGrothObj a' b' ** ?bbb) (MkGrothMor match (build . dia))
-- toGroth (MkPrism build match) = MkDepCoparaMor (MkGrothObj b' a' ** build) (MkGrothMor ?sss ?aaa )

leftPrism1 : Prism Int Int Unit Nat
leftPrism1 = MkPrism
  (fromInteger . cast)
  (\x => if x < 0 then Left () else Right (cast x))

leftPrism : {a, b, c : _} -> (arr CoCartOptic) (MkGrothObj (Either a c) (Either b c)) (MkGrothObj a b)
leftPrism = MkDepCoparaMor (MkGrothObj c c ** id) (MkGrothMor id id)

PrismToDepPrism : {A, B : AdtObj}
  -> (arr CoCartOptic) A B
  -> (arr (DepOpticCat CoCartDepAdt)) (AdtObjToCont0 A) (AdtObjToCont0 B)
PrismToDepPrism (MkDepCoparaMor (MkGrothObj rbase rfib ** s) (MkGrothMor fwd bwd)) = MkDepCoparaMor
  (MkGrothObj rbase (\0 _ => rfib) ** s)
  $ MkGrothMor
    fwd
    wc
    where wc : (0 a0 : A .baseObj) -> Either0 (fwd a0) (\0 _ => B .fibObj) (\0 _ => rfib) -> A .fibObj
          wc a0 x with 0 (fwd a0)
            wc a0 x | with_pat with (x)
              wc a0 x | (Left x') | (IsLeft y) = bwd (Left y)
              wc a0 x | (Right x') | (IsRight y) = bwd (Right y)

