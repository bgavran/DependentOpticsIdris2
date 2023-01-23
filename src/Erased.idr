
module Erased

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

