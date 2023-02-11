module BiCoPara

import Data.DPair


--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- After writing st of this file I realised that we don't want dependence on B.
-- In prisms, we might never go the way of B.
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- covariant in one variable, contravariant in other?
public export
biDependent : (a, b : Type) -> Type
biDependent a b = (a -> b -> Type) -> Type

-- Pi type into dependent pair
public export
sigmaPi : {A, B : Type} -> biDependent A B
sigmaPi res = (a : A) -> (b : B ** res a b)

-- Pi type into a coproduct B + (0 a : A ** B a)
public export
exists : {A, B : Type} -> biDependent A B
exists res = (a : A) -> Either B (Exists (res a))

-- this is reparamCoParaMor!?
-- in coproduct of B and M we can't know for sure whether B happened
-- in coproduct of B and (\_ => M) we also don't know whether B happened, since we might get something of type M, and
-- coproduct of B and M has always secretly been a coproduct of B and something of type (0 b:B ** r b) where 'b' is erased information at runtime
e : {B, M : Type} -> Either B M -> Either B (Exists (\_ => M))
e bm = case bm of
  Left b => Left b
  Right m => Right (Evidence ?aa m)
-- this is an issue with Idris that I can't implement this
-- if the function is constant, then this means I don't need to provide fst

public export
record BiDepCartCoPara (A, B : Type) where
  constructor MkBiDepCartCoPara
  resB : A -> B -> Type
  fwB : (a : A) -> (b : B ** resB a b) -- B doesn't necessarily have to happen!!!!

public export
compBiDepCartCoPara: {A, B, C : Type} -> BiDepCartCoPara A B -> BiDepCartCoPara B C -> BiDepCartCoPara A C
compBiDepCartCoPara f g = MkBiDepCartCoPara
  (\a, c => (b : B ** Pair (resB f a b) (resB g b c)))
  (\a => let bm = fwB f a
             cn = fwB g (fst bm)
         in (fst cn ** (fst bm ** (snd bm, snd cn))))


public export
record BiDepCoPara (A, B : Type) (s : biDependent A B) where
  constructor MkBiDepCoPara
  resB : A -> B -> Type
  fwB : s resB


-- fff : {A, B : Type} -> BiDepCoPara A B (exists {A} {B}) -> A -> Type
-- fff (MkBiDepCoPara rr ff) = \a => let t = (ff a)
--                                   in ?lol

-- public export
-- compBiDepCoPara: {A, B, C : Type} -> BiDepCoPara A B -> BiDepCoPara B C -> BiDepCoPara A C
-- compBiDepCoPara f g = MkBiDepCoPara
--   ?rr
--   ?fw
