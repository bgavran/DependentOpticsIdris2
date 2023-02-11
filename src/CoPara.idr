module CoPara

import Data.DPair

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Cartesian dependent Copara
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
record CartDepCoPara (A, B : Type) where
  constructor MkCartDepCoPara
  res1 : A -> Type
  fw1 : (a : A) -> Pair B (res1 a)

-- this looks really complex just because I can't use let bindings in Idris.
public export
compCartDepCoPara: {A, B, C : Type} -> CartDepCoPara A B -> CartDepCoPara B C -> CartDepCoPara A C
compCartDepCoPara f g = MkCartDepCoPara
  (\a => Pair (res1 f a) (res1 g (fst (fw1 f a))))
  (\a => (fst ((fw1 g) (fst ((fw1 f) a))), (snd ((fw1 f) a), snd ((fw1 g) (fst ((fw1 f) a))))))

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- CoCartesian dependent Copara
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- CoPara as a section of C/A -> C, i.e. a functor C -> C/A


-- Para([A, Set]) includes r:A -> Set and a map (now need to choose monoidal product) f:a

public export
record CocartDepCoPara (A, B : Type) where
  constructor MkCocartDepCoPara
  res1 : A -> Type
  fw1 : (a : A) -> Either B (res1 a)

-- can join, but not separate? something laxy is going on here. this is because we don't have to run either of the maps to go one way
-- can't go back because if you get a map f : (a : A) -> Either B (r a) you might've actually gotten *two* kinds of maps from two parts of A - one that goes to B, and one that goes to r a
-- but you don't know anything about this without computing f first
joinn : {A, B : Type}
  -> {r : A -> Type}
  -> Either (A -> B) ((a : A) -> r a)
  -> ((a : A) -> Either B (r a)) -- this might not consist of a ap to B at all
joinn (Left fb) = \a => Left (fb a)
joinn (Right fr) = \a => Right (fr a)


-- going backwards would give us a pair of maps whose domains would be subsets of A
-- but we'd have to trace things out, and run this computation first?
-- separate : {A, B : Type}
--   -> {r : A -> Type}
--   -> ((a : A) -> Either B (r a)) -- this might not consist of a ap to B at all
--   -> Either (A -> B) ((a : A) -> r a)
-- separate = ?ui

-- F(A) -> F(A)
public export
compCocartDepCoPara: {A, B, C : Type} -> CocartDepCoPara A B -> CocartDepCoPara B C -> CocartDepCoPara A C
compCocartDepCoPara f g = MkCocartDepCoPara
  (\a => Either (res1 f a) (b : B ** res1 g b))
  (\a => case fw1 f a of
      Left b => case fw1 g b of
         Left c => Left c
         Right n => Right (Right (b ** n))
      Right m => (Right (Left m)))


--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- More general forms of Copara
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- only works for Moncat TypeCat?
public export
record DepCoParaM (M : Type -> Type -> Type) (A, B : Type) where
  constructor MkDepCoParaM
  resM : A -> Type
  fwM : (a : A) -> M B (resM a)


{-
public export
compDepCoParaM : {A, B, C : Type} -> {M : Type -> Type -> Type}
  -> DepCoParaM M A B -> DepCoParaM M B C -> DepCoParaM M A C
compDepCoParaM f g = MkDepCoParaM
  (\a => let rm1 = resM f
             rm2 = resM g
             t = fwM f a
         in M (rm1 a) (b : B ** rm2 b)) -- the b that is fed in will always be from fw2
  (\a => let mb = (fwM f) a
         in ?fw) --(\a => (fst ((fw1 g) (fst ((fw1 f) a))), (snd ((fw1 f) a), snd ((fw1 g) (fst ((fw1 f) a))))))
