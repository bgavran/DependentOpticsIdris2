module ChurchForRealz

record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

opCat : Cat -> Cat
opCat c = MkCat c.obj (flip c.arr)

TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

FamCatOld : Cat
FamCatOld = MkCat
  (A : Type ** A -> Type)
  (\(a ** a'), (b ** b') => (f : a -> b ** (x : a) -> a' x -> b' (f x)))

FamCat : Type -> Cat
FamCat a = MkCat
  (a -> Type)
  (\a', b' => (x : a) -> a' x -> b' x)

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

IndFam : IndCat TypeCat
IndFam = MkIndCat FamCat (\a, b, c => b (a c))

DepCartAction : DepAct TypeCat
DepCartAction = MkDepAct IndFam DPair -- action is just forming the dependent pair

record DepCoPara (c : Cat) (m : DepAct c) (A, B : c.obj) where
  constructor MkDepCoPara
  0 M : (m.bund.mapObj B).obj
  f : c.arr A (m.act B M)

-- Example Type is a Cat

CartAction : DepAct TypeCat
CartAction = MkDepAct
  (MkIndCat (\_ => TypeCat) (\_ => id))
  (,)

graphCartCoPara : {A, B : Type} -> (A -> B) -> DepCoPara TypeCat CartAction A B
graphCartCoPara f = MkDepCoPara A (\a => (f a, a))


record OverDepAct (c : Cat) (m : DepAct c) (d : IndCat c) where
  constructor MkOverDepAct
  actt : (x : c.obj) -> (p : (m.bund.mapObj x).obj) -> (x' : (d.mapObj x).obj) -> (d.mapObj (m.act x p)).obj


fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkIndCat (opCat . ic.mapObj) ic.mapMor

-- forgetting A ??? :bomb:
groth : (c : Cat) -> IndCat c -> Cat
groth c indcat = MkCat
  (x : c.obj ** (indcat.mapObj x).obj)
  (\x, y => (g : c.arr x.fst y.fst ** (indcat.mapObj x.fst).arr x.snd (indcat.mapMor g y.snd) ))
  --(\(x ** x'), (y ** y') => (g : c.arr x y ** (indcat.mapObj x).arr ((indcat.mapMor g) y') x'))


forgett : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c) -> OverDepAct c m d -> DepAct (groth c d)
forgett c m d doa = MkDepAct
  (MkIndCat (\x => m.bund.mapObj x.fst) (\(f ** f') => m.bund.mapMor f))
  (\(x ** x'), x'' => (m.act x x'' ** doa.actt x x'' x') )


DependentOptics : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c) -> (over : OverDepAct c m (fibOp c d))
               -> (x : c.obj) -> (x' : ((fibOp c d).mapObj x).obj)
               -> (y : c.obj) -> (y' : ((fibOp c d).mapObj y).obj)
               -> Type
DependentOptics c m d over x x' y y' = DepCoPara (groth c (fibOp c d)) (forgett c m (fibOp c d) over) (x ** x') (y ** y')

-- x  -> y
-- x' <- y'
CartesianOptics : (x, x', y, y' : Type) -> Type
CartesianOptics x x' y y' = DependentOptics TypeCat CartAction (MkIndCat (\_ => TypeCat) (\_ => id))
  (MkOverDepAct (\z => \p => \w => Pair p w)) x x' y y'

record Cont where
  constructor MkCont
  pos : Type
  dir : pos -> Type


DepCartesianOptics : Cont -> Cont -> Type
DepCartesianOptics (MkCont a a') (MkCont b b') = DependentOptics
  TypeCat
  DepCartAction
  IndFam
  (MkOverDepAct (\x, p, x', dp => ?ll))
  a
  a'
  b
  b'


{-
ContMor : Cont -> Cont -> Type
ContMor (MkCont p1 d1) (MkCont p2 d2) =
  DependentOptics TypeCat DepCartAction IndFam ?o ?p1 ?d1 ?p2 ?d2

testOptic : CartesianOptics (a, b) (a', b) a a'
testOptic = MkDepCoPara (a, b) (MkDPair (\p => (fst p, p)) (\x => (snd x, snd (fst x))))



























{-


SliceCat : Type -> Cat
SliceCat a = MkCat
  (x : Type ** x -> a)
  (\(x ** p), (y ** q) => x -> y) -- missing proof that triangle commutes


graphDepCoPara : {A : Type} -> {B : A -> Type} -> ((a : A) -> B a) -> DepCoPara TypeCat DepCartAction A (a : A ** B a)
graphDepCoPara f = MkDepCoPara (\(a ** a') => ?ll) (\a => ?xx)

graphDepCoPara' : {A : Type} -> {B : A -> Type} -> ((a : A) -> B a) -> DepCoPara TypeCat DepCartAction A A
graphDepCoPara' f = MkDepCoPara B (\x => (x ** f x))
