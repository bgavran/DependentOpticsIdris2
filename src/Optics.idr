module Optics

import Cats
import Groth
import Erased
import DepAct
import WeightedCopara
import Misc

import Data.Either

OpticCat : (c, d, m : Cat)
  -> (a : NonDepAct (Adt c d) (Adt m m))
  -> Cat
OpticCat c d m a = WeightedCoparaCat
  (Adt c d)
  (Adt m m)
  a
  Hom

DepOpticCat : (a : NonDepAct (DepAdt TypeCat) (DepAdt TypeCat)) -> Cat
DepOpticCat a = WeightedCoparaCat
  (DepAdt TypeCat)
  (DepAdt TypeCat)
  a
  DepHom

TwoActionsToOptic : (c, d, m : Cat)
  -> (l : NonDepAct c m)
  -> (r : NonDepAct d m)
  -> Cat
TwoActionsToOptic c d m l r = OpticCat c d m (TwoActionsToAdtAction c d m m l r)

CoCartOptic : Cat
CoCartOptic = TwoActionsToOptic TypeCat TypeCat TypeCat CoCartAction CoCartAction

CartOptic : Cat
CartOptic = TwoActionsToOptic TypeCat TypeCat TypeCat CartAction CartAction

Grate : Cat
Grate = TwoActionsToOptic TypeCat TypeCat TypeCat HomAction CartAction

AffTraversal : Cat
AffTraversal = TwoActionsToOptic TypeCat TypeCat (productCat TypeCat TypeCat)  AffTraversalAct AffTraversalAct

-- ArbHom : {A, B : AdtObj}
--   -> (arr CartOptic) A B
--   -> Type
-- ArbHom (MkWCoparaMor (MkGrothObj ?mm ?oo) ?s (MkGrothMor ?ff ?bb)) = ?ee



CartOpticToDepOptic : Functor CartOptic (DepOpticCat (DepAdtNonDepAct CartAction))
CartOpticToDepOptic = MkFunctor (AdtToDepAdt .mapObj)
  $ \(MkWCoparaMor m s (MkGrothMor f f')) => MkWCoparaMor
    (AdtToDepAdt .mapObj m)
    s
    (MkGrothMor f (\0 _ => f'))

LensToCartOpticMor : {A, B : ConstCont}
  -> (arr Lens) A B
  -> (arr CartOptic) (ConstContToAdtObj A) (ConstContToAdtObj B)
LensToCartOpticMor {A=a} (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj a.baseObj)
  id
  (MkGrothMor (graph f) (f' . swap))

LensToCartOptic : Functor Lens CartOptic
LensToCartOptic = MkFunctor ConstContToAdtObj LensToCartOpticMor

LensToClosedFormMor : {a, b : ConstCont}
  -> (arr Lens) a b
  -> (arr CartOptic) (ConstContToAdtObj a) (ConstContToAdtObj b)
LensToClosedFormMor (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj (b.fibObj -> a.fibObj))
  (curry f')
  $ MkGrothMor
    (graph f)
    (\x => (snd x) (fst x))

LensToClosedForm : Functor Lens CartOptic
LensToClosedForm = MkFunctor ConstContToAdtObj LensToClosedFormMor

lm : {a, b : Cont} ->
     {f : a .baseObj -> b .baseObj} ->
     {f' : (x : a .baseObj) -> b .fibObj (f x) -> a .fibObj x} ->
     (0 a0 : a.baseObj ) ->
     (b .fibObj (f a0) , PairProof (a.baseObj) a0) -> a.fibObj a0
lm a0 (b', MkPairProof aRes p) = let b'' = cong {a = a0} {b=aRes} (\x => b.fibObj (f x)) (p)
                                     v = f' aRes (replace {p = id} b'' b') in
                                     replace {p = \x => a.fibObj x} (sym p) v

DepLensToDepOpticMor : {a, b : Cont}
  -> (arr (DepLens TypeCat)) a b
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) (ContToContAdt a) (ContToContAdt b)
DepLensToDepOpticMor (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj (PairProof a.baseObj))
  (\a => MkPairProof a Refl)
  (MkGrothMor (graph f) (lm {f} {f'} {a} {b}))


DepLensToDepOptic : Functor (DepLens TypeCat) (DepOpticCat (DepAdtNonDepAct CartAction))
DepLensToDepOptic = MkFunctor ContToContAdt DepLensToDepOpticMor

DepLensToClosedFormMor : {a, b : Cont}
  -> (arr (DepLens TypeCat)) a b
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) (ContToContAdt a) (ContToContAdt b)
DepLensToClosedFormMor (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj a.baseObj (\a0 => b.fibObj (f a0) -> a.fibObj a0))
  f'
  (MkGrothMor (graph f) (\0 _ => eval))

DepLensToClosedForm : Functor (DepLens TypeCat) (DepOpticCat (DepAdtNonDepAct CartAction))
DepLensToClosedForm = MkFunctor ContToContAdt DepLensToClosedFormMor

DepAdtToDepOpticMor : {A, B : ContAdt}
  -> (arr (DepAdt TypeCat)) A B
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) A B
DepAdtToDepOpticMor (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj () (\_ => ()))
  id
  $ MkGrothMor
  (\a => (f a, ()))
  (\0 a0, x => f' a0 (fst x))

DepAdtToDepOptic : Functor (DepAdt TypeCat) (DepOpticCat (DepAdtNonDepAct CartAction))
DepAdtToDepOptic = MkFunctor id $ \(MkGrothMor f f') => MkWCoparaMor
  (MkGrothObj () (\_ => ()))
  id
  (MkGrothMor (\a => (f a, ())) (\0 a0, x => f' a0 (fst x)))

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

PrismToDepPrismMor : {A, B : AdtObj}
  -> (arr CoCartOptic) A B
  -> (arr (DepOpticCat CoCartDepAdt)) (AdtToDepAdt .mapObj A) (AdtToDepAdt .mapObj B)
PrismToDepPrismMor (MkWCoparaMor (MkGrothObj rbase rfib) s (MkGrothMor fwd bwd)) = MkWCoparaMor
  (MkGrothObj rbase (\_ => rfib))
  s
  $ MkGrothMor
    fwd
    wc
    where wc : (0 a0 : A .baseObj) -> Either0 (fwd a0) (\_ => B .fibObj) (\_ => rfib) -> A .fibObj
          wc a0 x with 0 (fwd a0)
            wc a0 x | with_pat with (x)
              wc a0 x | (Left x') | (IsLeft y) = bwd (Left y)
              wc a0 x | (Right x') | (IsRight y) = bwd (Right y)


CoCartOpticToDepCoCartOptic : Functor CoCartOptic (DepOpticCat CoCartDepAdt)
CoCartOpticToDepCoCartOptic = MkFunctor (AdtToDepAdt .mapObj) PrismToDepPrismMor
