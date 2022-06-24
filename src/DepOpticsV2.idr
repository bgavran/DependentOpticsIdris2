module DepOpticsV2
-- This is version 2 that doesn't work yet. The idea is to not to use projections to define it, and instead use CoPara. It breaks in the record DepOptic

pairFns : (a -> Type) -> (c -> Type) -> Pair a c -> Type
pairFns f g (a, c) = Pair (f a) (g c)

record Cont  where
  constructor MkCont
  pos : Type
  dir : pos -> Type

-- The constant container
Const : Type -> Type -> Cont
Const ty1 ty2 = MkCont ty1 (const ty2)

record DAdapter (A, B : Cont) where
  constructor MkDAdapter
  fw  : (pos A) -> pos B
  bw : {0 a : pos A} -> dir B (fw a) -> dir A a
  
record Adapter (A, A', B, B' : Type) where
  constructor MkAdapter
  adapter : DAdapter (Const A A') (Const B B')
  
record DLens (A, B : Cont) where
  constructor MkDLens
  fw  : (pos A) -> pos B
  bw : {a : pos A} -> dir B (fw a) -> dir A a
  
record Lens (A, A', B, B' : Type) where
  constructor MkLens
  lens : DLens (Const A A') (Const B B')
  
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
  f : (pos A) -> Pair res (pos B) -- f a : (res, pos B)
  f' : {0 a : pos A} -> DepOpticsV2.pairFns (\x => res) (dir B) (f a) -> dir A a

-- Andre: This might be what you are looking for? It feels like it makes more sense than having a `const` function returning `res`
-- This is the same as having an existential Cont
record VarDepOptic (A, B : Cont) where
  constructor MkVarDepOptic
  res : Type
  next : res -> Type
  f : (pos A) -> Pair res (pos B)
  f' : {0 a : pos A} -> pairFns next (dir B) (f a) -> dir A a

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
