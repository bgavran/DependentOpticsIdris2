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
sigmaPi : {A, B : Type} -> (A -> (B -> Type)) -> Type
sigmaPi res = (a : A) -> (b : B ** res a b)

public export
record DepCoPara (A, B : Type) where
  constructor MkDepCoPara
  res : A -> (B -> Type)
  fw : sigmaPi res

public export
compRes : {A, B, C : Type} -> (A -> (B -> Type)) -> (B -> (C -> Type)) -> (A -> (C -> Type))
compRes r1 r2 = \a, c => (b : B ** (r1 a b, r2 b c))

public export
compDepCoPara : {A, B, C : Type} -> DepCoPara A B -> DepCoPara B C -> DepCoPara A C
compDepCoPara f g = MkDepCoPara
  (compRes (res f) (res g))
  (\a => let (b ** r1) = (fw f) a
             (c ** r2) = (fw g) b
         in (c ** b ** (r1, r2)))

public export
CoParaToDepCoPara : {A, B : Type} -> CoPara A B -> DepCoPara A B
CoParaToDepCoPara (MkCoPara m f) = MkDepCoPara (\_, _ => m) ((\(b, mm) => (b ** mm)) . f)
