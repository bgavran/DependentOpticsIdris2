module Cats

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

-- Functors are defined by their action on objects
public export
0 Functor : Cat -> Cat -> Type
Functor c d = c.obj -> d.obj

-- An indexed category is a functor C^op -> Cat
public export
record IndCat (c : Cat) where
  constructor MkIndCat
  mapObj : c.obj -> Cat
  mapMor : {x, y : c.obj} -> c.arr x y -> Functor (mapObj y) (mapObj x)
-- to rewrite indexed category as a functor we also need to write the category of categories as a category

public export
0 IndFunctor : (c : Cat) -> (f, g : IndCat c) -> Type
IndFunctor c f g = (x : c.obj) -> Functor ((mapObj f) x) ((mapObj g) x)

public export
constCat : {c : Cat} -> (d : Cat) -> IndCat c
constCat d = MkIndCat (\_ => d) (\_ => id)

public export
fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkIndCat (opCat . ic.mapObj) ic.mapMor

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Examples of categories
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- There is a category of Idris types and functions
public export
TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Examples of functors
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- this function sholud in principle be the same as constCat!
public export
constFunctor : Type -> Functor c TypeCat
constFunctor t = \_ => t

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
FamInd c = MkIndCat (Fam c) (\f => (. f))

-- %%%%%%%
public export
CoKleisliCat : Type -> Cat
CoKleisliCat p = MkCat
  Type
  (\a, b => Pair p a -> b)

public export
CoKleisliInd : IndCat TypeCat
CoKleisliInd = MkIndCat CoKleisliCat (\_ => id) -- it does something on morphisms, but it's invisible here


-- %%%%%%%
-- For a category `c` and a type `a` there is a category of `0 : a`-indexed c objects
public export
Fam0 : (c : Cat) -> Type -> Cat
Fam0 c a = MkCat
  (a -> c.obj) -- does this have to be zero?
  (\a', b' => (0 x : a) -> c.arr (a' x) (b' x))

-- 0 is a functor Type -> Type
public export
Fam0Ind : (c : Cat) -> IndCat TypeCat
Fam0Ind c = MkIndCat (Fam0 c) (\f, a', x => a' (f x)) -- (\a => (. a))

fn : (arr TypeCat) Bool String
fn = \b => "lol"
