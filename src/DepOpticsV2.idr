module DepOpticsV2
-- This is version 2 that doesn't work yet. The idea is to not to use projections to define it, and instead use CoPara. It breaks in the record DepOptic

import Iso

record Container where
  constructor MkContainer
  pos : Type
  dir : pos -> Type

-- The constant container
Const : Type -> Container
Const ty = MkContainer ty (const ty)

Prod : Container -> Container -> Container
Prod a b = MkContainer (a.pos, b.pos) (\x => Either (a.dir (fst x)) (b.dir (snd x)))

Parallel : Container -> Container -> Container
Parallel a b = MkContainer (a.pos, b.pos) (\x => (a.dir (fst x), b.dir (snd x)))

PairFns : (a -> Type) -> (c -> Type) -> Pair a c -> Type
PairFns f g x = Pair (f (fst x)) (g (snd x))

-- Andre: This might be what you are looking for? It feels like it makes more sense than having a `const` function returning `res`
-- This is the same as having an existential Container
record Optic (a, b : Container) where
  constructor MkOptic
  0 c : Container
  f : a.pos -> Pair c.pos b.pos
  f' : {x : a.pos} -> PairFns c.dir b.dir (f x) -> a.dir x

lemmaFst : (x : a) -> fst (x, b) = x
lemmaFst _ = Refl

transport : x -> y = x -> y
transport z Refl = z

composition : Optic a b -> Optic b c -> Optic a c
composition (MkOptic res f f') (MkOptic res2 g g') = MkOptic
  (Parallel res res2)
  forward
  backward
  where
    forward : a.pos -> ((res.pos, res2.pos), c.pos)
    forward x = let r1 = f x
                    r2 = g (snd r1)
                in ((fst r1, fst r2), snd r2)
    backward : {x : a.pos} -> PairFns ((Parallel res res2).dir) (dir c) (forward x) -> dir a x
    backward ((y, w), z) with (f x) proof p
      backward ((y, w), z) | (res1Pos, bPos) with (g bPos) proof p'
        backward ((y, w), z) | (res1Pos, bPos) | (res2Pos, cPos) =
          f' (transport y (cong res.dir (cong fst p))
             , let ggg = g' ( transport w (cong res2.dir (cong fst p'))
                            , transport z (cong c.dir (cong snd p')))
               in transport ggg (cong b.dir (cong snd p)))

fork : (c -> a) -> (c -> b) -> c -> (a, b)
fork f g x = (f x, g x)

assoc : (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

assoc' : ((a, b), c) -> (a, (b, c))
assoc' ((a, b), c) = (a, (b, c))

-- Dependent lenses
record Lens (c1, c2 : Container) where
  constructor MkLens
  get : c1.pos -> c2.pos
  set : (x : c1.pos) -> c2.dir (get x) -> c1.dir x

compose : Lens c1 c2 -> Lens c2 c3 -> Lens c1 c3
compose (MkLens g1 s1) (MkLens g2 s2) = MkLens
  (g2 . g1)
  (\x, y => s1 x (s2 (g1 x) y))

embed : Lens c1 c2 -> Optic c1 c2
embed (MkLens get set) = MkOptic
  (MkContainer c1.pos (\x => c1.pos ))
  (\x => (x, get x))
  (\(k, y) => set (?shu ) (?sad))

Boundary : Type
Boundary = Pair Type Type

record PlainLens (b1, b2 : Boundary) where
  constructor MkPLens
  get : fst b1 -> fst b2
  set : fst b1 -> snd b2 -> snd b1

composePlainLens : PlainLens a b -> PlainLens b c -> PlainLens a c
composePlainLens l1 l2 = MkPLens
  (l2.get . l1.get)
  (curry $ uncurry l1.set . fork fst (uncurry l2.set . mapFst l1.get))

record PlainOptic (b1, b2 : Boundary) where
  constructor MkPOptic
  0 r : Type
  get : fst b1 -> (fst b2, r)
  set : (r, snd b2) -> snd b1

composePlainOptics : PlainOptic a b -> PlainOptic b c -> PlainOptic a c
composePlainOptics x y = MkPOptic
  (Pair x.r y.r)
  (\z => let v1 = x.get z ; v2 = y.get (fst v1) in (fst v2, (snd v1, snd v2)))
  (\z => x.set (fst (fst z), y.set (snd (fst z), snd z)))

embedPlain : PlainLens a b -> PlainOptic a b
embedPlain lens = MkPOptic
  (fst a)
  (\x => (lens.get x, x))
  (uncurry lens.set)

recover : (o : PlainOptic a b) -> PlainLens a b
recover opt =
  MkPLens (fst . opt.get) (\x, y => opt.set (snd (opt.get x) , y))

lensIsoOptic : PlainLens a b `Iso` PlainOptic a b
lensIsoOptic = MkIso
  embedPlain
  recover
  (\case (MkPLens get set) => Refl)
  (\case (MkPOptic r get set) => ?yepCantDoThisOne)


