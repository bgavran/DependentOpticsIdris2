-- This is version 1, that works.

record PolyObj  where
  constructor MkPolyObj
  pos : Type
  dir : pos -> Type

record DepOptic (A, B : PolyObj) where
  constructor MkDepOptic
  res : Type
  f : (pos A) -> Pair res (pos B)
  f' : {0 a : pos A} -> (r : res) -> dir B (snd (f a)) -> dir A a
  -- note that in f' above we have to use (snd (f a)), even though we're technically in monoidal category where we don't have projections. A more careful look shows that we don't really want to project - we want to pair it with res! 
-- We have a ---f----> (res, pos B) -----(1_res, dir B)----> (res, dir B (pos B))

comp : {A, B, C : PolyObj} -> DepOptic A B -> DepOptic B C -> DepOptic A C
comp (MkDepOptic m f f') (MkDepOptic n g g') = MkDepOptic
    (m, n)
    (\a => let mmb = f a
               nnc = g (snd mmb)
           in ((fst mmb, fst nnc), snd nnc)) -- if we use let (mm, b) = f a unification fails
    (\(mm, nn) => \c' => f' mm (g' nn c'))

po1 : PolyObj
po1 = MkPolyObj String (\x => String)

po2 : PolyObj
po2 = MkPolyObj Char (\x => Char)
