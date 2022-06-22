TT : Int -> Type
TT _ = Pair String Int

ff : TT 3
ff = ("abc", 3)



record PolyObj  where
  constructor MkPolyObj
  pos : Type
  dir : pos -> Type

-- is there already some syntax for this?
pairFns : (a -> b) -> (c -> d) -> Pair a c -> Pair b d
pairFns f g (a, c) = (f a, g c)

-- (res : Type, pos B : Type)

record DepOptic (A, B : PolyObj) where
  constructor MkDepOptic
  res : Type
  f : (pos A) -> Pair res (pos B) -- f a : (res, pos B)
  f' : {0 a : pos A} -> f a -> dir A a
  -- f' : {0 a : pos A} -> pairFns (id {a = res}) (dir B) (f a) -> dir A a
  -- f' : {0 a : pos A} -> (pairFns id (dir B)) f a : (res, Type)
  --f' : {0 a : pos A} -> (r : res) -> dir B (snd (f a)) -> dir A a

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

