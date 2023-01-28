module Test


lt : Nat -> Nat -> Bool
lt Z n = True
lt (S m) (S n) = lt m n
lt _ _ = False


t : Nat -> Type
t n = if (S Z `lt` n ) then Nat else (Nat, Nat)

f : (n : Nat) -> t n
f n with (S Z `lt` n)
  f n | True = n
  f n | False = (17, n)

g : (0 x : Int) -> (Int, Int)
g _ = (0, 0)

t' : Nat -> Type
t' n = case n > S Z of
  True => Nat
  False => (Nat, Nat)

f' : (n : Nat) -> t n
f' n = case n > S Z of
  True => ?n
  False => ?nn


record Unerase (A : Type) (0 a : A) where
  constructor MkUnerase
  a' : A
  p : a = a'

wtf : {A : Type} -> (0 a : A) -> Unerase A a -> A
wtf a (MkUnerase a' p) = a'

record ResidualProof (A, B : Type) (f : A -> B) (0 a : A) (0 b : B) where
  constructor MkResidualProof
  a0 : A
  p : a = a0
  q : b = f a
