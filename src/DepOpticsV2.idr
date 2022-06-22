module DepOpticsV2
-- This is version 2 that doesn't work yet. The idea is to not to use projections to define it, and instead use CoPara. It breaks in the record DepOptic

record PolyObj  where
  constructor MkPolyObj
  pos : Type
  dir : pos -> Type

-- The constant container
Const : Type -> PolyObj
Const ty = MkPolyObj ty (const ty)

Prod : PolyObj -> PolyObj -> PolyObj
Prod a b = MkPolyObj (a.pos, b.pos) (\x => Either (a.dir (fst x)) (b.dir (snd x)))

Parallel : PolyObj -> PolyObj -> PolyObj
Parallel a b = MkPolyObj (a.pos, b.pos) (\x => (a.dir (fst x), b.dir (snd x)))

PairFns : (a -> Type) -> (c -> Type) -> Pair a c -> Type
PairFns f g x = Pair (f (fst x)) (g (snd x))

record DepOptic (A, B : PolyObj) where
  constructor MkDepOptic
  res : Type
  f : (pos A) -> Pair res (pos B) -- f a : (res, pos B)
  f' : {0 a : pos A} -> PairFns (\x => res) (dir B) (f a) -> dir A a

-- Andre: This might be what you are looking for? It feels like it makes more sense than having a `const` function returning `res`
-- This is the same as having an existential PolyObj
record VarDepOptic (A, B : PolyObj) where
  constructor MkVarDepOptic
  c : PolyObj
  f : (pos A) -> Pair c.pos (pos B)
  f' : {x : pos A} -> PairFns c.dir (dir B) (f x) -> dir A x

lemmaFst : (x : a) -> fst (x, b) = x
lemmaFst _ = Refl

transport : x -> y = x -> y
transport z Refl = z

composition : VarDepOptic a b -> VarDepOptic b c -> VarDepOptic a c
composition (MkVarDepOptic res f f') (MkVarDepOptic res2 g g') = MkVarDepOptic
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



assoc : (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

assoc' : ((a, b), c) -> (a, (b, c))
assoc' ((a, b), c) = (a, (b, c))

-- coParaComp : (a -> (m, b)) -> (b -> (n, c)) -> (a -> ((m, n), c))
-- coParaComp f g = \a => assoc ((pairFns id g) (f a))


-- comp : {A, B, C : PolyObj} -> DepOptic A B -> DepOptic B C -> DepOptic A C
-- comp (MkDepOptic m mp f f') (MkDepOptic n np g g') = MkDepOptic
--     (m, n)
--     (mp . (pairFns id np) . assoc')
--     (coParaComp f g)
--     (\z => f' ?cop)
    --            (nn, c) = g b
    --        in ((mm, nn), c)) -- some unification fails when formulated like this?
    -- (\(mm, nn) => \c' => f' mm (g' nn ?wer))
    -- (\(mm, nn) => \c' => f' mm (g' nn c'))

po1 : PolyObj
po1 = MkPolyObj String (\x => String)

po2 : PolyObj
po2 = MkPolyObj Char (\x => Char)


  -- g : (A, B : PolyObj)
  --   -> (res : Type) -> (rp : (res, Type) -> Type)
  --   -> (f : pos A -> (res, pos B)) -> (a : pos A)
  --   -> Int
  -- g (MkPolyObj posA dirA) (MkPolyObj posB dirB) res rp f a
  --   = let e = pairFns (id {a = Int}) ?zz
  --         i = (rp . pairFns id dirB) . f
  --         j = i a
  --     in ?jj


TT : Int -> Type
TT _ = Pair String Int

ff : TT 3
ff = ("abc", 3)


