module Cats

import Misc

public export
record Cat where
  constructor MkCat
  0 obj : Type
  0 arr : obj -> obj -> Type

public export
opCat : Cat -> Cat
opCat c = MkCat c.obj (flip c.arr)

public export
productCat : (c : Cat) -> (d : Cat) -> Cat
productCat c d = MkCat (obj c, obj d) (\a, b => ((arr c) (fst a) (fst b), (arr d) (snd a) (snd b)))

public export
record Functor (c, d : Cat) where
  constructor MkFunctor
  0 mapObj : c.obj -> d.obj
  0 mapMor : {x, y : c.obj} -> c.arr x y -> d.arr (mapObj x) (mapObj y)

public export
idFunctor : (c : Cat) -> Functor c c
idFunctor c = MkFunctor id id

public export
opFunctor : {c, d : Cat} -> Functor c d -> Functor (opCat c) (opCat d)
opFunctor f = MkFunctor (mapObj f) (mapMor f)

public export
compFunctor : {c, d, e : Cat} -> Functor c d -> Functor d e -> Functor c e
compFunctor f g = MkFunctor (mapObj g . mapObj f) (mapMor g . mapMor f)

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Examples of categories
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- There is a category of Idris types and functions
public export
TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

public export
CatofCats : Cat
CatofCats = MkCat Cat Functor

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- IndCat stuff
--%%%%%%%%%%%%%%%%%%%%%%%%%--

public export
IndCat : (c : Cat) -> Type
IndCat c = Functor c (opCat CatofCats)

public export
0 IndFunctor : (c : Cat) -> (f, g : IndCat c) -> Type
IndFunctor c f g = (x : c.obj) -> Functor ((mapObj f) x) ((mapObj g) x)

public export
constCat : {c : Cat} -> (d : Cat) -> IndCat c
constCat d = MkFunctor (\_ => d) (\_ => idFunctor d)

public export
fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkFunctor (opCat . ic.mapObj) (opFunctor . ic.mapMor)

-- this function should in principle be the same as constCat
public export
constType : Type -> Functor c (opCat TypeCat)
constType t = MkFunctor (\_ => t) (\_ => id)

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Examples of indexed categories
--%%%%%%%%%%%%%%%%%%%%%%%%%--


-- %%%%%%%
-- For a category `c` and a type `a` there is a category of `a`-indexed c objects
public export
Fam : (c : Cat) -> Type -> Cat
Fam c a = MkCat
  (a -> c.obj)
  (\a', b' => (x : a) -> c.arr (a' x) (b' x))

-- And this is an indexed category over the category of types
public export
FamInd : (c : Cat) -> IndCat TypeCat
FamInd c = MkFunctor (Fam c) (\f => MkFunctor (. f) (\j, xx => j (f xx)))

DepFn : {x, y : Type}
  -> (x -> y)
  -> (x -> Type)
  -> (y -> Type)
DepFn f x' = \y => DFunction (a : x ** f a = y) (\(a ** p) => x' a)

DepPair : {x, y : Type}
  -> (x -> y)
  -> (x -> Type)
  -> (y -> Type)
DepPair f x' = \y => DPair (a : x ** f a = y) (\(a ** p) => x' a)

-- public export
-- FamIndDFun : Functor TypeCat CatofCats
-- FamIndDFun = MkFunctor
--   (Fam TypeCat)
--   (\f => MkFunctor (DepFn f) (\g, h, x => ?ezz))

-- FamIndDPair : (c : Cat) -> Functor TypeCat CatofCats
-- FamIndDPair c = MkFunctor
--   (Fam c)
--   (\f => MkFunctor (\x' => ?feff) ?ezzz)

-- %%%%%%%
public export
CoKleisli : Type -> Cat
CoKleisli p = MkCat
  Type
  (\a, b => Pair p a -> b)

public export
CoKleisliInd : IndCat TypeCat
CoKleisliInd = MkFunctor CoKleisli (\f => MkFunctor id (\g => g . (mapFst f)))

-- %%%%%%%
-- For a category `c` and a type `a` there is a category of `0 : a`-indexed c objects
public export
Fam0 : (c : Cat) -> Type -> Cat
Fam0 c a = MkCat
  (a -> c.obj)
  (\a', b' => (0 x : a) -> c.arr (a' x) (b' x))


-- 0 is a functor Type -> Type
public export
Fam0Ind : (c : Cat) -> IndCat TypeCat
Fam0Ind c = MkFunctor (Fam0 c) (\f => MkFunctor (. f) (\j, xx => j (f xx)))


fn : (arr TypeCat) Bool String
fn = \b => "lol"
