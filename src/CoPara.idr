module CoPara

public export
record CoPara (A, B : Type) where
  constructor MkCoPara
  M : Type
  f : A -> (B, M)

sigmaPi : {A, B : Type} -> (A -> (B -> Type)) -> Type
sigmaPi res = (a : A) -> (b : B ** res a b)

record DepCoPara (A, B : Type) where
  constructor MkDepCoPara
  res : A -> (B -> Type)
  f : sigmaPi res

CoParaToDepCoPara : {A, B : Type} -> CoPara A B -> DepCoPara A B
CoParaToDepCoPara (MkCoPara m f) = MkDepCoPara (\_, _ => m) ((\(b, m) => (b ** m)) . f)
