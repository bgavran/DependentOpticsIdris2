module DepOpticsV2

PairFns : (a -> Type) -> (c -> Type) -> Pair a c -> Type
PairFns f g (a, c) = Pair (f a) (g c)

record Cont  where
  constructor MkCont
  pos : Type
  dir : pos -> Type

-- The constant container
Const : Type -> Type -> Cont
Const ty1 ty2 = MkCont ty1 (const ty2)

-- Hancock, or Dirichlet product of containers
hancockProd : Cont -> Cont -> Cont
hancockProd c1 c2 = MkCont (pos c1, pos c2) (\px => (dir c1 (fst px), dir c2 (snd px)))

record DAdapter (A, B : Cont) where
  constructor MkDAdapter
  fw  : (pos A) -> pos B
  bw : {0 a : pos A} -> dir B (fw a) -> dir A a

Adapter : {A, A', B, B' : Type} -> Type
Adapter = DAdapter (Const A A') (Const B B')

record DLens (A, B : Cont) where
  constructor MkDLens
  fw  : (pos A) -> pos B
  bw : {a : pos A} -> dir B (fw a) -> dir A a

Lens : {A, A', B, B' : Type} -> Type
Lens = DLens (Const A A') (Const B B')

{-
There is a square where maps are embeddings
Adapter ---> DAdapter
  |            |
  |            |
  v            v
Lens    ---> DLens
-}

record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  res : Type
  f : (pos A) -> Pair res (pos B)
  f' : {0 a : pos A} -> PairFns (\x => res) (dir B) (f a) -> dir A a

embedDlDo : {A, B : Cont} -> DLens A B -> DepOptic A B
embedDlDo (MkDLens f f') = MkDepOptic (pos A) (\a => (a, f a)) (\(aa, b') => let tt = f'
                                                                             in ?tr)

record CPDepOptic (A, B : Cont) where
  constructor MkCPDepOptic
  res : Type
  f : DAdapter A (hancockProd (Const res res) B)

embedDlCpdo : {A, B : Cont} -> DLens A B -> CPDepOptic A B
embedDlCpdo (MkDLens f f') = MkCPDepOptic
  (pos A)
  (MkDAdapter
    (\a => (a, f a))
    ?ff)

assoc : (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

assoc' : ((a, b), c) -> (a, (b, c))
assoc' ((a, b), c) = (a, (b, c))

-- coParaComp : (a -> (m, b)) -> (b -> (n, c)) -> (a -> ((m, n), c))
-- coParaComp f g = \a => assoc ((pairFns id g) (f a))


-- comp : {A, B, C : Cont} -> DepOptic A B -> DepOptic B C -> DepOptic A C
-- comp (MkDepOptic m mp f f') (MkDepOptic n np g g') = MkDepOptic
--     (m, n)
--     (mp . (pairFns id np) . assoc')
--     (coParaComp f g)
--     (\z => f' ?cop)
    --            (nn, c) = g b
    --        in ((mm, nn), c)) -- some unification fails when formulated like this?
    -- (\(mm, nn) => \c' => f' mm (g' nn ?wer))
    -- (\(mm, nn) => \c' => f' mm (g' nn c'))
