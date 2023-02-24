module Cats

public export

public export

public export
productCat : (c : Cat) -> (d : Cat) -> Cat
productCat c d = MkCat (obj c, obj d) (\a, b => ((arr c) (fst a) (fst b), (arr d) (snd a) (snd b)))

-- Functors are defined by their action on objects
public export

-- An indexed category is a functor C^op -> Cat
public export
-- to rewrite indexed category as a functor we also need to write the category of categories as a category

public export
0 IndFunctor : (c : Cat) -> (f, g : IndCat c) -> Type
IndFunctor c f g = (x : c.obj) -> Functor ((mapObj f) x) ((mapObj g) x)

public export

public export

--%%%%%%%%%%%%%%%%%%%%%%%%%--
-- Examples of categories
--%%%%%%%%%%%%%%%%%%%%%%%%%--

-- There is a category of Idris types and functions
public export

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

-- And this is an indexed category over the category of types
public export

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

fn : (arr TypeCat) Bool String
fn = \b => "lol"
