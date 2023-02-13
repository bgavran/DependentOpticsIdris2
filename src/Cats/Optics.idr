module Cats.Optics

import Cats.Cats
import Cats.Groth
import Cats.Erased
import Cats.DepAct
import Cats.DepCoPara
import Cats.DepPara
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
-- ArbHom (MkDepCoparaMor (MkGrothObj (m, n) (m', n') ** (s, s')) (MkGrothMor f b)) = ?ee

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
  (MkGrothObj a.baseObj (Unerase a.baseObj) ** \a0 => MkUnerase a0 Refl)
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

{-
-- Prisms can't be made dependent!
-- forward pass?
CoCartOpticToDepOptic : {A, B : AdtObj}
  -> (arr CoCartOptic) A B
  -> (arr (DepOpticCat CoCartAdt)) (AdtObjToCont0 A) (AdtObjToCont0 B)
CoCartOpticToDepOptic {A=a} (MkDepCoparaMor ((MkGrothObj rb rf) ** s) (MkGrothMor m b)) = MkDepCoparaMor
  (MkGrothObj rb (\0 _ => rf) ** s)
  $ MkGrothMor
    m
    (\0 a0 => ?bb)
