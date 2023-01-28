module Cats.Cats

public export
record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

public export
opCat : Cat -> Cat
opCat c = MkCat c.obj (flip c.arr)

-- rewrite indexed category as a functor, but for that we'd also need to write the category of categories as a category

-- Functors are defined by their action on objects
public export
Functor : Cat -> Cat -> Type
Functor c d = c.obj -> d.obj

-- An indexed category is a functor C^op -> Cat
public export
record IndCat (c : Cat) where
  constructor MkIndCat
  mapObj : c.obj -> Cat
  mapMor : {x, y : c.obj} -> c.arr x y -> Functor (mapObj y) (mapObj x)

public export
fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkIndCat (opCat . ic.mapObj) ic.mapMor

----------------------------------------
-- Examples
----------------------------------------

-- There is a category of Idris types and functions
public export
TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

-- For a type `a` there is a category of `a`-indexed types

public export
FamCat : Type -> Cat
FamCat a = MkCat
  (a -> Type)
  (\a', b' => (x : a) -> a' x -> b' x)


-- And this is an indexed category over the category of types

public export
FamInd : IndCat TypeCat
FamInd = MkIndCat FamCat (\f => (. f))

-- For a type `a` there is a category of `a`-indexed types

public export
Fam0Cat : Type -> Cat
Fam0Cat a = MkCat
  ((0 x : a) -> Type)
  (\a', b' => (0 x : a) -> a' x -> b' x)


-- 0 is a functor Type -> Type
public export
Fam0Ind : IndCat TypeCat
Fam0Ind = MkIndCat Fam0Cat (\f, a', x => a' (f x)) -- (\a => (. a))
