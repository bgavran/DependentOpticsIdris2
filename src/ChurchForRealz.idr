module ChurchForRealz

import Data.Vect

record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

-- rewrite indexed category as a functor, but for that we'd also need to write the category of categories as a category

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

FLens : (c : Cat) -> (f : IndCat c) -> Cat
FLens c f = groth c (fibOp c f)

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
FamInd = MkIndCat FamCat (\f => (. f))

-- For a type `a` there is a category of `a`-indexed types
Fam0Cat : Type -> Cat
Fam0Cat a = MkCat
  ((0 x : a) -> Type)
  (\a', b' => (0 x : a) -> a' x -> b' x)

-- 0 is a functor Type -> Type

Fam0Ind : IndCat TypeCat
Fam0Ind = MkIndCat Fam0Cat (\f, a', x => a' (f x)) -- (\a => (. a))

DepAdt : Cat
DepAdt = FLens TypeCat Fam0Ind

data Fin0 : (0 n : Nat) -> Type where
  FZero : Fin0 (S n)
  FSucc : Fin0 n -> Fin0 (S n)

data Vect0 : (0 t : Type) -> (0 n : Nat) -> Type where
  Nil : Vect0 a Z
  (::) : e -> Vect0 e n -> Vect0 e (S n)

tail0 : Vect0 a (S n) -> Vect0 a n
tail0 (x :: y) = y

Domainobj : GrothObj TypeCat Fam0Ind
Domainobj = MkGrothObj Nat Fin0

Codomainobj : GrothObj TypeCat Fam0Ind
Codomainobj = MkGrothObj Nat Fin0

f : arr DepAdt (MkGrothObj Nat (Vect0 Bool)) (MkGrothObj Nat (Vect0 Bool))
f = MkGrothMor S (\x => tail0)

-- A dependent action on a category `c` is an indexed category over `c`
-- with an action of the fibres on their base.
record DepAct (c : Cat) where
  constructor MkDepAct
  bund : IndCat c
  act : (x : c.obj) -> Functor (bund.mapObj x) c
  -- we can uncurry this to become a functor from Groth construction to c


CartAction : DepAct TypeCat
CartAction = MkDepAct
  (MkIndCat (\_ => TypeCat) (\_ => id))
  (,)


DepCartAction : DepAct TypeCat
DepCartAction = MkDepAct FamInd DPair

DepCart0Action : DepAct TypeCat
DepCart0Action = MkDepAct Fam0Ind ?rr -- DPair

record CoparaMor (c : Cat) (m : DepAct c) (A, B : c.obj) where
  constructor MkCoparaMor
  0 M : (m.bund.mapObj B).obj
  f : c.arr A (m.act B M)


CoparaCat : (c : Cat) -> (m : DepAct c) -> Cat
CoparaCat c m = MkCat c.obj (CoparaMor c m)


-- String -> Nat involves an Nat-indexed Set, r:Nat -> Set and then
-- the function f : String -> (n : Nat ** r n)
CoparaFamInd : CoparaMor TypeCat DepCartAction String Nat
CoparaFamInd = MkCoparaMor (flip Vect Bool) (\s => (_ ** map (== 'a') (fromList (unpack s))))


-- Example, the graph of a function is a coparameterised morphism
graphCartCoPara : {A, B : Type} -> (A -> B) -> CoparaMor TypeCat CartAction A B
graphCartCoPara f = MkCoparaMor A (\a => (f a, a))


-- Data we need to specify the action per fiber
record OverDepAct (c : Cat) (action : DepAct c) (d : IndCat c) where
  constructor MkOverDepAct
  actt : (y : c.obj)
          -> (m : (action.bund.mapObj y).obj)
          -> (y' : ((fibOp c d).mapObj y).obj)
          -> ((fibOp c d).mapObj (action.act y m)).obj

-- Combine two X-indexed sets into one indexed sets
-- FamInd appears twice, once in DepCartAction and once here in type
-- Indexed by the dependent pair, but functionally doesn't depend on it
i : (y : Type) -- You get a set Y
  -> (m : y -> Type) -> (y' : y -> Type) -- You get 2 Y-indexed sets
  -> (y0 : y ** m y0) -> Type -- Create a (y0 : y ** m y)-indexed Set
i y m y' = \(y0 ** m0) => y' y0 -- by only indexing over y0 using y'
-- i y m = (mapMor FamInd) fst -- by only indexing over y0 using y'

CospanOverAct : OverDepAct TypeCat DepCartAction FamInd
CospanOverAct = MkOverDepAct (\y, m => (mapMor FamInd) fst)

-- drops the base, FamInd is here two times
-- FamInd is inside DepAct
-- FamInd is d
-- TODO refactor this
GrothAct : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c)
          -> OverDepAct c m d
          -> DepAct (FLens c d)
GrothAct c m d doa = MkDepAct
  -- what this says is that the things that can act on (x, x') in D^ are exactly the things that can act on x in C (where C <-- D^)
  (MkIndCat (\x => m.bund.mapObj x.baseObj) (\f => m.bund.mapMor f.baseMor)) -- doubly indexed category (i.e. indexed over the total space)
  (\(MkGrothObj xbase xpoint), m' => MkGrothObj (m.act xbase m') (doa.actt xbase m' xpoint))

-- Dependent optics is CoPara of something
-- CoPara(Cont)
DependentOpticsCat : (c : Cat) -> (m : DepAct c) -> (d : IndCat c)
                     -> (over : OverDepAct c m d)
                     -> Cat
DependentOpticsCat c m d over = CoparaCat (FLens c d) (GrothAct c m d over)

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
CartesianOptic x x' y y' = DependentOptics TypeCat CartAction       (MkIndCat (\_ => TypeCat) (\_ => id))
  (MkOverDepAct (\_ => Pair)) x x' y y'

graph : (a -> b) -> (a -> (b, a))
graph f = \a => (f a, a)

embedLensintoDepOptic : (a -> b) -> ((a, b') -> a') -> CartesianOptic a a' b b'
embedLensintoDepOptic f fsharp = MkCoparaMor a (MkGrothMor (graph f) fsharp)

-- objects of Fam(Set) are containers
Cont : Type
Cont = GrothObj TypeCat (fibOp TypeCat FamInd)

-- using FamInd twice below!
CartDepOptics : Cat
CartDepOptics = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct

record DLens (a : Cont) (b : Cont) where
  constructor MkDLens
  fwd : a.baseObj -> b.baseObj
  bck : (x : a.baseObj) -> b.fibObj (fwd x) -> a.fibObj x

record ClDLens (a : Cont) (b : Cont) where
  constructor MkClDLens
  cl : (x : a.baseObj) -> (y : b.baseObj ** b.fibObj y -> a.fibObj x)

DepGraph : (f : a -> b) -> (a -> (x : b ** a))
DepGraph f a = (f a ** a)

-- DLenstoDepOptic : (A, B : Cont) -> DLens A B -> (arr CartDepOptics) A B
-- DLenstoDepOptic (MkGrothObj a a') (MkGrothObj b b') (MkDLens f f') = MkCoparaMor
--   (\_ => a)
--   (MkGrothMor (DepGraph f) ?bwl) -- f')

-- testDepOptic : (arr CartDepOptics) (MkGrothObj String (\s => ())) (MkGrothObj () (\_ => ()))
-- testDepOptic = MkCoparaMor
--   (?tt)
--   (MkGrothMor (\s => (() ** ?l)) ?bw)


{-
ClDLenstoDepOptic : (A, B : Cont) -> ClDLens A B -> (arr CartDepOptics) A B
ClDLenstoDepOptic (MkGrothObj a a') (MkGrothObj b b') (MkClDLens cl)= MkCoparaMor
-- TODO put 0 x here, ask Andre
  (\b => Bool)-- (x : a ** b' b -> a' x)) -- needs to hold (fst cl) x = b
  (MkGrothMor
    ?fw -- (\x => (fst (cl x) ** (x ** snd (cl x))))
    ?bw)

-- because we don't know that fst (cl x) = ?
-- DLenstoDepOptic (MkGrothObj aPos aDir) (MkGrothObj bPos bDir)
        --(\x => a.baseObj)
  --(MkGrothMor
  --  (graph f.fwd)
  --  f.bck)
