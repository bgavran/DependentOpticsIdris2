module ChurchForRealz

record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

Functor : Cat -> Cat -> Type
Functor c d = c.obj -> d.obj

-- C^op -> Cat
record IndCat (c : Cat) where
  constructor MkIndCat
  mapObj : c.obj -> Cat
  mapMor : {x, y : c.obj} -> c.arr x y -> Functor (mapObj y) (mapObj x)

record DepAct (c : Cat) where
  constructor MkDepAct
  bund : IndCat c
  act : (x : c.obj) -> (bund.mapObj x).obj -> c.obj

record DepCoPara (c : Cat) (m : DepAct c) (A, B : c.obj) where
  constructor MkDepCoPara
  0 M : (m.bund.mapObj B).obj
  f : c.arr A (m.act B M)

-- Example Type is a Cat

TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

CartAction : DepAct TypeCat
CartAction = MkDepAct
  (MkIndCat (\_ => TypeCat) (\_ => id))
  (,)

graphCartCoPara : {A, B : Type} -> (A -> B) -> DepCoPara TypeCat CartAction A B
graphCartCoPara f = MkDepCoPara A (\a => (f a, a))


record OverDepAct (c : Cat) (m : DepAct c) (d : IndCat c) where
  constructor MkOverDepAct
  actt : (x : c.obj) -> (p : (m.bund.mapObj x).obj) -> (x' : (d.mapObj x).obj) -> (d.mapObj (m.act x p)).obj

-- forgetting A ??? :bomb:
groth : (c : Cat) -> IndCat c -> Cat
groth c indcat = MkCat
  (x : c.obj ** (indcat.mapObj x).obj)
  (\x, y => (g : c.arr x.fst y.fst ** (indcat.mapObj x.fst).arr ((indcat.mapMor g) y.snd) x.snd))
  --(\(x ** x'), (y ** y') => (g : c.arr x y ** (indcat.mapObj x).arr ((indcat.mapMor g) y') x'))

forgett : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c) -> OverDepAct c m d -> DepAct (groth c d)
forgett c m d doa = MkDepAct
  (MkIndCat (\x => m.bund.mapObj x.fst) (\(f ** f') => m.bund.mapMor f))
  (\(x ** x'), x'' => (m.act x x'' ** doa.actt ?ee ?rr ?tt) )


-- ff : (A : Type) -> (B : A -> Type) -> Type
-- ff a f = (x : a ** f x)


























{-

FamCat : Cat
FamCat = MkCat
  (A : Type ** A -> Type)
  (\(a ** a'), (b ** b') => (f : a -> b ** (x : a) -> a' x -> b' (f x)))

SliceCat : Type -> Cat
SliceCat a = MkCat
  (x : Type ** x -> a)
  (\(x ** p), (y ** q) => x -> y) -- missing proof that triangle commutes

IndCat : Type -> Cat
IndCat a = MkCat
  (a -> Type)
  (\a', b' => (x : a) -> a' x -> b' x)

DepCartAction : DepAct TypeCat
DepCartAction = MkDepAct IndCat (\x, f => (y : x ** f y))

graphDepCoPara : {A : Type} -> {B : A -> Type} -> ((a : A) -> B a) -> DepCoPara TypeCat DepCartAction A (a : A ** B a)
graphDepCoPara f = MkDepCoPara (\(a ** a') => ?ll) (\a => ?xx)

graphDepCoPara' : {A : Type} -> {B : A -> Type} -> ((a : A) -> B a) -> DepCoPara TypeCat DepCartAction A A
graphDepCoPara' f = MkDepCoPara B (\x => (x ** f x))
