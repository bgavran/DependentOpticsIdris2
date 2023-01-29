module CoPara

public export
record CoPara (A, B : Type) where
  constructor MkCoPara
  res : Type
  f : A -> (B, res)

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

graphCoPara : {A, B : Type} -> (A -> B) -> CoPara A B
graphCoPara f = MkCoPara A (graph f)

public export
sigmaPi : {A, B : Type} -> ((0 _ : A) -> (0 _ : B) -> Type) -> Type
sigmaPi res = (a : A) -> (b : B ** res a b)

public export
record DepCoPara (A, B : Type) where
  constructor MkDepCoPara
  res1 : A -> Type
  fw1 : (a : A) -> (B, res1 a)

-- Important! We're still just over A!
public export
compRes1 : {A, B, C : Type} -> ((0 _ : A) -> Type) -> ((0 _ : B) -> Type) -> ((0 _ : A) -> Type)
compRes1 r1 _ = r1

-- this looks really complex just because I can't use let bindings in Idris.
public export
compDepCoPara : {A, B, C : Type} -> DepCoPara A B -> DepCoPara B C -> DepCoPara A C
compDepCoPara f g = MkDepCoPara
  (\a => (res1 f a, res1 g (fst (fw1 f a))))
  (\a => (fst ((fw1 g) (fst ((fw1 f) a))), (snd ((fw1 f) a), snd ((fw1 g) (fst ((fw1 f) a))))))


public export
record DepCoParaM (M : Type -> Type -> Type) (A, B : Type) where
  constructor MkDepCoParaM
  resM : A -> Type
  fwM : (a : A) -> M B (resM a)


public export
compDepCoParaM : {A, B, C : Type} -> {M : Type -> Type -> Type}
  -> DepCoParaM M A B -> DepCoParaM M B C -> DepCoParaM M A C
compDepCoParaM f g = MkDepCoParaM
  (\a => let rm1 = resM f
             rm2 = resM g
             t = fwM f a
         in M (rm1 a) (rm2 ?bb)) -- (resM f a, resM g (fst (fwM f a))))
  ?lol --(\a => (fst ((fw1 g) (fst ((fw1 f) a))), (snd ((fw1 f) a), snd ((fw1 g) (fst ((fw1 f) a))))))
