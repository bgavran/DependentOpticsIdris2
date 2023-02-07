module Cats.Optics

import Cats.Cats
import Cats.Groth
import Cats.Erased
import Cats.DepAct
import Cats.DepCoPara
import Cats.DepPara

-- Tw(M) acts on Adapters!!!
-- Tw(M) is sections of Adapters?
OpticAct : (c : Cat)
  -> (d : Cat)
  -> (m : Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d m)
  -> NonDepAct (Adt c d) (TwistedArr m)
OpticAct c d m l r = MkDepAct $ \(MkGrothObj x x'), (m ** _) =>
  (MkGrothObj ((act l) x m.baseObj) ((act r) x' m.fibObj))

-- -- rewrite this just using  AdtNonDepAct, see how it doesn't work
-- AlmostOpticCat :
--      (l : NonDepAct TypeCat TypeCat)
--   -> (r : NonDepAct TypeCat TypeCat)
--   -> Cat
-- AlmostOpticsCat = DepCoparaCat (Adt TypeCat TypeCat) (constCat (Adt TypeCat TypeCat)) ()

OpticCat : (c : Cat)
  -> (d : Cat)
  -> (m : Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d m)
  -> Cat
OpticCat c d m l r = DepCoparaCat (Adt c d) (constCat (TwistedArr m)) (OpticAct c d m l r)

BimorphicLensToOptic :
  --    (l : NonDepAct TypeCat TypeCat)
  -- -> (r : NonDepAct TypeCat TypeCat)
     (a, b, a', b' : Type)
  -> (arr BimorphicLens) (MkGrothObj a a') (MkGrothObj b b')
  -> (arr (OpticCat TypeCat TypeCat TypeCat CartAction CartAction)) (MkGrothObj a a') (MkGrothObj b b')
BimorphicLensToOptic a b a' b' (MkGrothMor f f') = MkDepCoparaMor
  (MkGrothObj a a ** ?xy)
  $ MkGrothMor
    (\a => (f a, ?ee))
    (f' . swap)

record NonDepOpticMor
  (c : Cat)
  (d : Cat)
  (m : Cat)
  (l : NonDepAct c m)
  (r : NonDepAct d m)
  (a, b : c.obj)
  (a', b' : d.obj)
  where
  constructor MkNonDepOpticMor
  fw : DepCoparaMor c (constCat m) l a b
  bw : DepParaMor d (constCat m) r b' a'
  resEqual : (M fw) = (M bw)


mor : (a, b, a', b' : Type)
  -> (arr BimorphicLens) (MkGrothObj a a') (MkGrothObj b b')
  -> NonDepOpticMor TypeCat TypeCat TypeCat CartAction CartAction a b a' b'
mor a b a' b' (MkGrothMor f f') = MkNonDepOpticMor
  (MkDepCoparaMor a (\a => (f a, a)))
  (MkDepParaMor a (\x => f' (snd x, fst x)))
  Refl



CoparaCartAdt : Cat
CoparaCartAdt = DepCoparaCat (Adt TypeCat TypeCat) (constCat (Adt TypeCat TypeCat)) (e1 (AdtNonDepAct CartAction))

-- every optic embeds into Copara(Adt)? But there's more stuff in Copara(Adt)
-- if we add a vertical costate to Copara, we're still in adapters! no information actually flows back.
CoparaCartDepLensMor :  (a, b, a', b' : Type)
  -> NonDepOpticMor TypeCat TypeCat TypeCat CartAction CartAction a b a' b'
  -> (arr CoparaCartAdt) (MkGrothObj a a') (MkGrothObj b b')
CoparaCartDepLensMor a b a' b' (MkNonDepOpticMor fw bw re) = MkDepCoparaMor
  (MkGrothObj (M fw) (M bw))
  (MkGrothMor (f fw) (f bw))
