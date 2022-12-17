module ChurchForRealz

record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

-- Functors are defined by their action on objects
Functor : Cat -> Cat -> Type
Functor c d = c.obj -> d.obj

-- An indexed category is a functor C^op -> Cat
record IndCat (c : Cat) where
  constructor MkIndCat
  mapObj : c.obj -> Cat
  mapMor : {x, y : c.obj} -> c.arr x y -> Functor (mapObj y) (mapObj x)

opCat : Cat -> Cat
opCat c = MkCat c.obj (flip c.arr)

fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkIndCat (opCat . ic.mapObj) ic.mapMor

record GrothObj (c : Cat) (d: IndCat c) where
  constructor MkGrothObj
  baseObj : c.obj
  fibObj : (d.mapObj baseObj).obj

record GrothMor (c : Cat) (d : IndCat c) (s : GrothObj c d) (t : GrothObj c d) where
  constructor MkGrothMor 
  baseMor : c.arr s.baseObj t.baseObj
  fibMor : (d.mapObj s.baseObj).arr 
              s.fibObj
              (d.mapMor {x = s.baseObj} {y = t.baseObj} (baseMor) t.fibObj)

groth : (c : Cat) -> IndCat c -> Cat
groth c ind = MkCat
  (GrothObj c ind)
  (GrothMor c ind)

-- There is a category of Idris types and functions
TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

-- For a type `a` there is a category of `a`-indexed types
FamCat : Type -> Cat
FamCat a = MkCat
  (a -> Type)
  (\a', b' => (x : a) -> a' x -> b' x)

-- And this is an indexed category over the category of types
FamInd : IndCat TypeCat
FamInd = MkIndCat FamCat (\a, b => b . a)

-- A dependent action on a category `c` is an indexed category over `c`
-- with an action of the fibres on their base.
record DepAct (c : Cat) where
  constructor MkDepAct
  bund : IndCat c
  -- act : Functor (groth c bund) c
  act : (x : c.obj) -> Functor (bund.mapObj x) c


CartAction : DepAct TypeCat
CartAction = MkDepAct
  (MkIndCat (\_ => TypeCat) (\_ => id))
  (,)


DepCartAction : DepAct TypeCat
DepCartAction = MkDepAct FamInd DPair


record CoparaMor (c : Cat) (m : DepAct c) (A, B : c.obj) where
  constructor MkCoparaMor
  0 M : (m.bund.mapObj B).obj
  f : c.arr A (m.act B M)


CoparaCat : (c : Cat) -> (m : DepAct c) -> Cat
CoparaCat c m = MkCat c.obj (CoparaMor c m)


-- Example, the graph of a function is a coparameterised morphism
graphCartCoPara : {A, B : Type} -> (A -> B) -> CoparaMor TypeCat CartAction A B
graphCartCoPara f = MkCoparaMor A (\a => (f a, a))


record OverDepAct (c : Cat) (action : DepAct c) (d : IndCat c) where
  constructor MkOverDepAct
  actt : (x : c.obj) 
          -> (m : (action.bund.mapObj x).obj) 
          -> (x' : ((fibOp c d).mapObj x).obj) 
          -> ((fibOp c d).mapObj (action.act x m)).obj

forgett : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c) 
          -> OverDepAct c m d 
          -> DepAct (groth c (fibOp c d))
forgett c m d doa = MkDepAct
  (MkIndCat (\x => m.bund.mapObj x.baseObj) (\f => m.bund.mapMor (f.baseMor)))
  (\x, x'' => MkGrothObj (m.act x.baseObj x'') (doa.actt x.baseObj x'' x.fibObj) )

DependentOpticsCat : (c : Cat) -> (m : DepAct c) -> (d : IndCat c)
                     -> (over : OverDepAct c m d)
                     -> Cat
DependentOpticsCat c m d over = CoparaCat (groth c (fibOp c d)) (forgett c m d over)

DependentOptics : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c) 
               -> (over : OverDepAct c m d)
               -> (x : c.obj) -> (x' : ((fibOp c d).mapObj x).obj)
               -> (y : c.obj) -> (y' : ((fibOp c d).mapObj y).obj)
               -> Type
DependentOptics c m d over x x' y y' =
  (DependentOpticsCat c m d over).arr (MkGrothObj x x') (MkGrothObj y y')


-- x  -> y
-- x' <- y'
CartesianOptic : (x, x', y, y' : Type) -> Type
CartesianOptic x x' y y' = DependentOptics TypeCat CartAction (MkIndCat (\_ => TypeCat) (\_ => id))
  (MkOverDepAct (\_ => Pair)) x x' y y'

testOptics : (a -> b) -> (a -> b' -> a') -> CartesianOptic a a' b b'
testOptics f fsharp = MkCoparaMor a (MkGrothMor (\x => (f x, x)) (uncurry fsharp))

Cont = GrothObj TypeCat (fibOp TypeCat FamInd)

CospanOverAct : OverDepAct TypeCat DepCartAction FamInd
CospanOverAct = MkOverDepAct (\c, f, g => g . fst)

CartDepOptics : Cat
CartDepOptics = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct


record ContMor (a : Cont) (b : Cont) where
  fwd : a.baseObj -> b.baseObj
  bck : (x : a.baseObj) -> b.fibObj (fwd x) -> a.fibObj x

graph : (f : a -> b) -> (a -> (x : b ** a))
graph f a = (f a ** a)

testDependentOptics : (a, b : Cont) -> ContMor a b -> (arr CartDepOptics) a b
testDependentOptics a b f = MkCoparaMor
  (\x => a.baseObj)
  (MkGrothMor
    (graph f.fwd)
    f.bck)




























{-


SliceCat : Type -> Cat
SliceCat a = MkCat
  (x : Type ** x -> a)
  (\(x ** p), (y ** q) => x -> y) -- missing proof that triangle commutes


graphDepCoPara : {A : Type} -> {B : A -> Type} -> ((a : A) -> B a) -> DepCoPara TypeCat DepCartAction A (a : A ** B a)
graphDepCoPara f = MkDepCoPara (\(a ** a') => ?ll) (\a => ?xx)

graphDepCoPara' : {A : Type} -> {B : A -> Type} -> ((a : A) -> B a) -> DepCoPara TypeCat DepCartAction A A
graphDepCoPara' f = MkDepCoPara B (\x => (x ** f x))
