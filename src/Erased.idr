module Erased

import Data.Either
import Data.DPair


public export
data Fin0 : (0 n : Nat) -> Type where
  FZero : Fin0 (S n)
  FSucc : Fin0 n -> Fin0 (S n)

public export
data Vect0 : (0 t : Type) -> (0 n : Nat) -> Type where
  Nil : Vect0 a Z
  (::) : e -> Vect0 e n -> Vect0 e (S n)

public export
tail0 : Vect0 a (S n) -> Vect0 a n
tail0 (x :: y) = y

public export
map : (f : a -> b) -> Vect0 a n -> Vect0 b n
map f [] = []
map f (x :: y) = f x :: map f y

public export
length : Vect0 n a -> Nat
length [] = Z
length (x :: y) = S (length y)

-- public export
-- fromList : (xs : List elem) -> Vect0 elem (length xs)
-- fromList [] = []
-- fromList (x :: xs) = x :: fromList xs


public export
erasedReparam : {A, B : Type} -> {B' : B -> Type} ->
  (f : A -> B) -> ((0 b : B) -> B' b) -> (0 a : A) -> B' (f a)
erasedReparam f r = \a => r (f a)

public export
record Exists0 (type : Type) (p : (0 _ : type) -> Type) where
  constructor Ev
  0 fst : type
  snd : p fst

embed : DPair a b -> Exists b
embed (a ** b) = Evidence a b

-- hh : (x, y : Exists b) -> Type
-- hh x y = ?ell

Trm : a -> Type
Trm _ = ()

-- Given A:C, we call a pair (Z:C, e:A -> C) an erased A iff it is the coequaliser of every pair of morphisms into A.

-- data MyExists : (P : a -> Type) -> Type where
--   Evidence : @0 (x : a) -> (pf : P x) -> Exists P

-- vv : {A : Type} -> A -> Exists {a=A} Trm
-- vv a = Evidence ?aal ?aff

-- out : Exists b -> ?el

public export
record Subset0 (type : Type) (0 p : (0 _ : type) -> Type ) where
  constructor El
  fst : type
  0 snd : p fst

mapEither :
     ((0 _ : a) -> c)
  -> ((0 _ : b) -> d)
  -> (e : Either a b)
  -> Either c d
mapEither f g (Left a) = Left (f a)
mapEither f g (Right b) = Right (g b)

%unbound_implicits off
export 0
bimapLeft : forall a, a', b, b'.
            {f : a -> a'} -> {g : b -> b'} ->
            (x0 : Either a b) ->
            (y : a') ->
            bimap f g x0 === Left y -> (v ** (x0 === Left v, f v === y))
bimapLeft (Left val) y refl = (val ** (Refl, injective refl))
bimapLeft (Right val) y refl = absurd refl

export 0
bimapRight : forall a, a', b, b'.
            {f : a -> a'} -> {g : b -> b'} ->
            (x0 : Either a b) ->
            (y : b') ->
            bimap f g x0 === Right y -> (v ** (x0 === Right v, g v === y))
bimapRight (Left val) y refl = absurd refl
bimapRight (Right val) y refl = (val ** (Refl, injective refl))

%unbound_implicits on

public export
data EitherCheck : (0 _ : Either a b) -> (a -> Type) -> (b -> Type) -> Type where
  IsLeft' : {0 x : a} -> {0 f : a -> Type} -> {0 e : Either a b} -> f x ->
            (check : e === Left x) -> EitherCheck e f g
  IsRight' : {0 x : b} -> {0 g : b -> Type} -> {0 e : Either a b} -> g x ->
             (check : e = Right x) -> EitherCheck e f g

