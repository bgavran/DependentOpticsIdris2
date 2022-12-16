module ChurchForRealz

record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

indCat : Type -> Type
indCat x = x -> Cat

record DepAct (c : Cat) where
  constructor MkDepAct
  bund : indCat c.obj
  act : (x : c.obj) -> (bund x).obj -> c.obj

record DepCoPara (c : Cat) (m : DepAct c) (A, B : c.obj) where
  constructor MkDepCoPara
  0 M : (m.bund B).obj
  f : c.arr A (m.act B M)

-- Example Type is a Cat

TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

CartAction : DepAct TypeCat
CartAction = MkDepAct (\_ => TypeCat) (,)

graphCartCoPara : {A, B : Type} -> (A -> B) -> DepCoPara TypeCat CartAction A B
graphCartCoPara f = MkDepCoPara A (\a => (f a, a))

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
