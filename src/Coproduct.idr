module Coproduct

import Data.DPair

public export
data (+) x y = L x | R y

public export
Choice : Bool -> Type -> Type -> Type
Choice True a b = a
Choice False a b = b

public export
Choice' : Bool -> a -> b -> a + b
Choice' True a b = L a
Choice' False a b = R b

public export
0 DSum : (a : Type) -> (a -> Type) -> Type
DSum a f = Exists $ \x : a => Subset a (\y => x = y) + f x

public export
sym : a + b -> b + a
sym (L x) = R x
sym (R x) = L x

public export
elim : (a -> c) -> (b -> c) -> a + b -> c
elim f g (L x) = f x
elim f g (R x) = g x

public export
0 Elim : (a -> Type) -> (b -> Type) -> (choice : Bool) -> Choice choice a b -> Type
Elim f g False x = g x
Elim f g True x = f x

export
toChoice : a + b -> (c : Bool ** Choice c a b)
toChoice (L x) = (True ** x)
toChoice (R x) = (False ** x)


public export
fromBool : Bool -> a -> b -> a + b
fromBool False x y = R y
fromBool True x y = L x


public export
Bifunctor (+) where
  bimap f g = elim (L . f) (R . g)

public export
elim' : {0 c : a -> Type} -> {0 d : b -> Type} ->
        (f : (x : a) -> c x) -> (g : (x : b) -> d x) -> (p : a + b) -> (elim c d p)
elim' f g (L x) = f x
elim' f g (R x) = g x
