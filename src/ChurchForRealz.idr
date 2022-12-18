module ChurchForRealz

import Data.Vect

record Cat where
  constructor MkCat
  obj : Type
  arr : obj -> obj -> Type

-- Functors are defined by their action on objects
record Functor (c, d : Cat)  where
  constructor MkFunctor
  mapObj : c.obj -> d.obj
  mapMor : {a, b : c.obj} ->
           c.arr a b -> d.arr (mapObj a) (mapObj b)

Cat1Op : Cat
Cat1Op = MkCat Cat (\x, y =>  Functor y x)

-- TODO: change into functor
-- An indexed category is a functor C^op -> Cat
-- record IndCat (c : Cat) where
--   constructor MkIndCat
--   mapObj : c.obj -> Cat
--   mapMor : {x, y : c.obj} -> c.arr x y -> Functor (mapObj y) (mapObj x)

IndCat : (c : Cat) -> Type
IndCat c = Functor c Cat1Op

opCat : Cat -> Cat
opCat c = MkCat c.obj (flip c.arr)

fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkFunctor (opCat . ic.mapObj)
                       (\a => MkFunctor (ic.mapMor a).mapObj (ic.mapMor a).mapMor)

record GrothObj (c : Cat) (d: IndCat c) where
  constructor MkGrothObj
  baseObj : c.obj
  fibObj : (d.mapObj baseObj).obj

record GrothMor (c : Cat) (d : IndCat c) (s : GrothObj c d) (t : GrothObj c d) where
  constructor MkGrothMor
  baseMor : c.arr s.baseObj t.baseObj
  fibMor : (d.mapObj s.baseObj).arr
              s.fibObj
              ((d.mapMor {a = s.baseObj} {b = t.baseObj}
                    baseMor).mapObj t.fibObj)

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
FamInd = MkFunctor FamCat (\a => MkFunctor (. a) (\f, x, y => f (a x) y) )

-- A dependent action on a category `c` is an indexed category over `c`
-- with an action of the fibres on their base.
record DepAct (c : Cat) where
  constructor MkDepAct
  bund : IndCat c
  act : Functor (groth c bund) c -- Functor (bund.mapObj x) c

helpMe : {c : Cat} -> (d : DepAct c) -> (o : c.obj) -> (d.bund.mapObj o).obj -> c.obj -- Functor (bund.mapObj x) c
helpMe d o x = d.act.mapObj $ MkGrothObj o x

(.godHelpMe) : {c : Cat} -> (d : DepAct c) -> {o, o' : c.obj} ->
               (a : c.arr o o') ->
               {dio : (d.bund.mapObj o).obj} -> {dio' : (d.bund.mapObj o').obj} ->
               (d.bund.mapObj o).arr dio ((d.bund.mapMor {a = o} {b = o'} a).mapObj dio') ->
               c.arr (ChurchForRealz.helpMe d o dio) (ChurchForRealz.helpMe d o' dio')
(.godHelpMe) d a mor = d.act.mapMor $ MkGrothMor a mor

CartAction : DepAct TypeCat
CartAction = MkDepAct
  (MkFunctor (\_ => TypeCat) (\_ => MkFunctor (\x => x) (\x => x)))
  (MkFunctor (\x => Pair x.baseObj x.fibObj) (\(MkGrothMor f g) => bimap f g))

DepCartAction : DepAct TypeCat
DepCartAction = MkDepAct FamInd (MkFunctor (\x => DPair x.baseObj x.fibObj)
                                           (\d, v => MkDPair (d.baseMor v.fst) (d.fibMor v.fst v.snd)))

record CoparaMor (c : Cat) (m : DepAct c) (a, b : c.obj) where
  constructor MkCoparaMor
  res : (m.bund.mapObj b).obj
  f : c.arr a (m.act.mapObj (MkGrothObj b res))


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
      -> ((fibOp c d).mapObj (action.act.mapObj (MkGrothObj y m))).obj

  mort : {o, o' : c.obj}
      -> {dio : (action.bund.mapObj o).obj}
      -> {dio' : (action.bund.mapObj o').obj}
      -> {thing1 : ((fibOp c d).mapObj o).obj}
      -> {thing2 : ((fibOp c d).mapObj o').obj}
      -> (a : c.arr o o')
      -> (m : (action.bund.mapObj o).arr dio ((action.bund.mapMor {a = o} {b = o'} a).mapObj dio'))
      -> ((fibOp c d).mapObj o).arr thing1 (((fibOp c d).mapMor {a = o} {b = o'} a).mapObj thing2)
      -> ((fibOp c d).mapObj (helpMe action o dio)).arr
            (actt o dio thing1)
            (((fibOp c d).mapMor {a = helpMe action o dio} {b = helpMe action o' dio'}
                (action.godHelpMe {o} {o'} {dio'} {dio} a m)).mapObj
                (actt o' dio' thing2))

-- Combine two X-indexed sets into one indexed sets


-- FamInd appears twice, once in DepCartAction and once here in type

-- Indexed by the dependent pair, but functionally doesn't depend on it
i : (y : Type) -- You get a set Y
  -> (m : y -> Type) -> (y' : y -> Type) -- You get 2 Y-indexed sets
  -> (y0 : y ** m y0) -> Type -- Create a (y0 : y ** m y)-indexed Set
i y m y' = \(y0 ** m0) => y' y0 -- by only indexing over y0 using y'
-- i y m = (mapMor FamInd) fst -- by only indexing over y0 using y'

CospanOverAct : OverDepAct TypeCat DepCartAction FamInd
CospanOverAct = MkOverDepAct (\y, m, z => z . fst)
                             (\a, b, f, z, w => f (z.fst) w)

-- drops the base, FamInd is here two times
-- FamInd is inside DepAct
-- FamInd is d
GrothAct : (c : Cat) ->  (m : DepAct c) -> (d : IndCat c)
          -> OverDepAct c m d
          -> DepAct (groth c (fibOp c d))
GrothAct c m d doa = MkDepAct
  (MkFunctor (\x => m.bund.mapObj x.baseObj) (\f => m.bund.mapMor f.baseMor)) -- doubly indexed category (i.e. indexed over the total space) ((x ** x') => )
  (MkFunctor (\o => MkGrothObj (helpMe m o.baseObj.baseObj o.fibObj) (doa.actt o.baseObj.baseObj o.fibObj o.baseObj.fibObj))
             (\(MkGrothMor (MkGrothMor f f') g) => MkGrothMor
               (m.godHelpMe f g)
               (doa.mort f g f')))
  --(MkIndCat (\x => m.bund.mapObj x.baseObj) (\f => m.bund.mapMor (f.baseMor)))
  --(\x, x'' => MkGrothObj (m.act x.baseObj x'') (doa.actt x.baseObj x'' x.fibObj) )


DependentOpticsCat : (c : Cat) -> (m : DepAct c) -> (d : IndCat c)
                     -> (over : OverDepAct c m d)
                     -> Cat
DependentOpticsCat c m d over = CoparaCat (groth c (fibOp c d)) (GrothAct c m d over)

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
CartesianOptic x x' y y' = DependentOptics TypeCat CartAction
  (MkFunctor (\_ => TypeCat) (\_ => MkFunctor (\x => x) (\x => x)))
  (MkOverDepAct (\_ => Pair) (\_, f, g => ?makeitEnd)) x x' y y'

-- uncomment
-- testOptics : (a -> b) -> (a -> b' -> a') -> CartesianOptic a a' b b'
-- testOptics f fsharp = MkCoparaMor a (MkGrothMor (\x => (f x, x)) (uncurry fsharp))

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

graph : (f : a -> b) -> (a -> (x : b ** a))
graph f a = (f a ** a)

-- DLenstoDepOptic : (a, b : Cont) -> DLens a b -> (arr CartDepOptics) a b
-- DLenstoDepOptic (MkGrothObj aPos aDir) (MkGrothObj bPos bDir) (MkDLens f f') = MkCoparaMor
--   (\_ => aPos)
--   (MkGrothMor
--     (\a => (f a ** a))
--     ?fffffff)


-- DLenstoDepOptic : (a, b : Cont) -> ClDLens a b -> (arr CartDepOptics) a b
-- DLenstoDepOptic (MkGrothObj aPos aDir) (MkGrothObj bPos bDir)
        --(\x => a.baseObj)
  --(MkGrothMor
  --  (graph f.fwd)
  --  f.bck)

