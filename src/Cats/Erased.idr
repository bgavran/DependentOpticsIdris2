module Cats.Erased

import Data.Either

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

public export
fromList : (xs : List elem) -> Vect0 elem (length xs)
fromList [] = []
fromList (x :: xs) = x :: fromList xs


public export
erasedReparam : {A, B : Type} -> {B' : B -> Type} ->
  (f : A -> B) -> ((0 b : B) -> B' b) -> (0 a : A) -> B' (f a)
erasedReparam f r = \a => r (f a)

public export
record Exists0 (type : Type) (p : (0 _ : type) -> Type) where
  constructor Ev
  0 fst : type
  snd : p fst

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


public export
record Unerase (A : Type) (0 a : A) where
  constructor MkUnerase
  aRes : A
  p : a = aRes


public export
data Either0 : (0 _ : Either a b) ->
               ((0 _ : a) -> Type) ->
               ((0 _ : b) -> Type) -> Type where
  IsLeft : {0 x : a} -> {0 f : (0 _ : a) -> Type} ->
           f x -> Either0 (Left x) f g
  IsRight : {0 x : b} -> {0 g : (0 _ : b) -> Type} ->
            g x -> Either0 (Right x) f g

-- dependent eliminator for Either0
public export
elimEither0 : {0 a : Type} -> {0 a' : (0 _ : a) -> Type} ->
              {0 b : Type} -> {0 b' : (0 _ : b) -> Type} ->
              (0 e : Either a b) ->
              {0 m : {0 e : Either a b} -> Either0 e a' b' -> Type} ->
              (f : (0 x : a) -> (y : a' x) -> m (IsLeft y)) ->
              (g : (0 x : b) -> (y : b' x) -> m (IsRight y)) ->
              (v : Either0 e a' b') -> m v
elimEither0 (Left x) f g (IsLeft y) = f x y
elimEither0 (Right x) f g (IsRight y) = g x y

public export
elimEither0' : {0 a : Type} -> {0 a' : (0 _ : a) -> Type} ->
              {0 b : Type} -> {0 b' : (0 _ : b) -> Type} ->
              (0 e : Either a b) ->
              {0 m : Either a b -> Type} ->
              (f : (0 x : a) -> (y : a' x) -> m (Left x)) ->
              (g : (0 x : b) -> (y : b' x) -> m (Right x)) ->
              (v : Either0 e a' b') -> m e
elimEither0' (Left x) f g (IsLeft y) = f x y
elimEither0' (Right x) f g (IsRight y) = g x y

