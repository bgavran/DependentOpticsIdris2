record Cont where
  constructor MkCont
  pos : Type
  dir : pos -> Type


pairFns : (a -> b) -> (c -> d) -> Pair a c -> Pair b d
pairFns f g (a, c) = (f a, g c)

hancockProd : Cont -> Cont -> Cont
hancockProd c1 c2 = MkCont (pos c1, pos c2) (\px => (dir c1 (fst px), dir c2 (snd px)))

record DLens (A, B : Cont) where
  constructor MkDLens
  fw : pos A -> pos B
  bw : {a : pos A} -> dir B (fw a) -> dir A a


record DepOptic (A, B : Cont) where
  constructor MkDepOptic
  res : Cont
  f : DLens A (hancockProd res B)
  -- f : pos A -> (pos res, pos B)
  -- f' : {0 a : pos A} -> (dir (hancockProd res B)) (f a) -> dir A a

-- a -----f-----> (res, pos B) -----(dir res', dir B) ----> (Type, dir B (pos B))

assoc : (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

assoc' : ((a, b), c) -> (a, (b, c))
assoc' ((a, b), c) = (a, (b, c))

coParaComp : (a -> (m, b)) -> (b -> (n, c)) -> (a -> ((m, n), c))
coParaComp f g = \a => assoc ((pairFns id g) (f a))

coParaComp' : {A, B, C, M, N : Cont} -> DLens A (hancockProd M B) -> DLens B (hancockProd N C) -> DLens A (hancockProd (hancockProd M N) C)
coParaComp' (MkDLens fw bw) (MkDLens fw' bw') =
  MkDLens
  (\a => let mmb = fw a
             nnc = fw' (snd mmb)
         in ((fst mmb, fst nnc), snd nnc))
  (\(m, n) => bw ?asdfr)

-- comp : {A, B, C : Cont} -> DepOptic A B -> DepOptic B C -> DepOptic A C
-- comp (MkDepOptic r (MkDLens fw bw)) (MkDepOptic s (MkDLens fw' bw')) = MkDepOptic
--   (hancockProd r s)
--   (MkDLens (\a => let mmb = fw a
--                       nnc = fw' (snd mmb)
--                   in ((fst mmb, fst nnc), snd nnc)) -- if we use let (mm, b) = f a unification fails
--     (\((m, n), c') => bw ?asdf))
