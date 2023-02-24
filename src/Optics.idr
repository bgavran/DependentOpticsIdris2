module Optics


record Cat where
  constructor MkCat
  0 obj : Type
  0 arr : obj -> obj -> Type

0 Functor : Cat -> Cat -> Type
Functor c d = c.obj -> d.obj

record IndCat (c : Cat) where
  constructor MkIndCat
  mapObj : c.obj -> Cat
  mapMor : {x, y : c.obj} -> c.arr x y -> Functor (mapObj y) (mapObj x)

TypeCat : Cat
TypeCat = MkCat Type (\a, b => a -> b)

record GrothObj (c : Cat) (d: IndCat c) where
  constructor MkGrothObj
  baseObj : c.obj
  fibObj : (d.mapObj baseObj).obj

record GrothMor (c : Cat) (d : IndCat c) (s : GrothObj c d) (t : GrothObj c d) where
  constructor MkGrothMor
  baseMor : c.arr s.baseObj t.baseObj
  fibMor : (d.mapObj s.baseObj).arr
           s.fibObj
           (d.mapMor {x = s.baseObj} {y = t.baseObj} baseMor t.fibObj)

groth : (c : Cat) -> IndCat c -> Cat
groth c ind = MkCat
  (GrothObj c ind)
  (GrothMor c ind)

opCat : Cat -> Cat
opCat c = MkCat c.obj (flip c.arr)

fibOp : (c : Cat) -> IndCat c -> IndCat c
fibOp c ic = MkIndCat (opCat . ic.mapObj) ic.mapMor

FLens : (c : Cat) -> (f : IndCat c) -> Cat
FLens c f = groth c (fibOp c f)

public export
Fam0 : (c : Cat) -> Type -> Cat
Fam0 c a = MkCat
  (a -> c.obj) -- does this have to be zero?
  (\a', b' => (0 x : a) -> c.arr (a' x) (b' x))

-- 0 is a functor Type -> Type
public export
Fam0Ind : (c : Cat) -> IndCat TypeCat
Fam0Ind c = MkIndCat (Fam0 c) (\f, a', x => a' (f x)) -- (\a => (. a))

DepAdt : (d : Cat) -> Cat
DepAdt d = FLens TypeCat (Fam0Ind d)

record DepAct (c : Cat) (bund : IndCat c) where
  constructor MkDepAct
  act : (x : c.obj) -> Functor (bund.mapObj x) c

constCat : {c : Cat} -> (d : Cat) -> IndCat c
constCat d = MkIndCat (\_ => d) (\_ => id)

NonDepAct : (c, m : Cat) -> Type
NonDepAct c m = DepAct c (constCat m)

record WeightedCoparaMor
  (c : Cat)
  (m : Cat)
  (ac : NonDepAct c m)
  (s : Functor m TypeCat) -- for dep optics s also has to be a monoidal functor (this is because we need to be able to write composition)
  (A, B : c.obj) where
  constructor MkWCoparaMor
  M : m.obj
  S : s M
  f : c.arr A (ac.act B M)

WeightedCoparaCat : (c : Cat) -> (m : Cat) -> (ac : NonDepAct c m) -> (0 s : Functor m TypeCat) -> Cat
WeightedCoparaCat c m ac s = MkCat c.obj (WeightedCoparaMor c m ac s)

DFunction : (A : Type) -> (A' : A -> Type) -> Type
DFunction a a' = (x : a) -> a' x

DepOpticCat : (a : NonDepAct (DepAdt TypeCat) (DepAdt TypeCat)) -> Cat
DepOpticCat a = WeightedCoparaCat
  (DepAdt TypeCat)
  (DepAdt TypeCat)
  a
  (\mm => DFunction (mm.baseObj) (\x => mm.fibObj x))

Cont0 : Type
Cont0 = GrothObj TypeCat (fibOp TypeCat (Fam0Ind TypeCat))

Fam : (c : Cat) -> Type -> Cat
Fam c a = MkCat
  (a -> c.obj)
  (\a', b' => (x : a) -> c.arr (a' x) (b' x))

FamInd : (c : Cat) -> IndCat TypeCat
FamInd c = MkIndCat (Fam c) (\f => (. f))

DepLens : (d : Cat) -> Cat
DepLens d = FLens TypeCat (FamInd d)

Cont : Type
Cont = GrothObj TypeCat (fibOp TypeCat (FamInd TypeCat))

Cont0ToCont : Cont0 -> Cont
Cont0ToCont dd = MkGrothObj dd.baseObj dd.fibObj

DepAdtNonDepAct : NonDepAct TypeCat TypeCat -> NonDepAct (DepAdt TypeCat) (DepAdt TypeCat)
DepAdtNonDepAct ac = MkDepAct $ \aa', bb' => (MkGrothObj
  (Pair aa'.baseObj bb'.baseObj)
  (\x => (act ac) (aa'.fibObj (fst x)) (bb'.fibObj (snd x))))

CartAction : NonDepAct TypeCat TypeCat
CartAction = MkDepAct Pair

record PairProof (A : Type) (a : A) where
  constructor MkPairProof
  aRes : A
  p : a = aRes

graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

DepLensToDepOptic : {a, b : Cont0}
  -> (arr (DepLens TypeCat)) (Cont0ToCont a) (Cont0ToCont b)
  -> (arr (DepOpticCat (DepAdtNonDepAct CartAction))) a b
DepLensToDepOptic  (MkGrothMor f f') = MkWCoparaMor
  (MkGrothObj (a.baseObj) (PairProof (a.baseObj)))
  (\a => MkPairProof a Refl)
  $ MkGrothMor
    (graph f)
    ?hole
    -- (\0 x, (b', prf) => ?mmm)
