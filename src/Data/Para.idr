module Data.Para

public export
record Para (A, B : Type) where
  constructor MkPara
  res : Type
  f : (res, A) -> B

-- sigmaPi : {A, B : Type} -> (A -> (B -> Type)) -> Type
-- sigmaPi res = (a : A) -> (b : B ** res a b)

record DepPara (A, B : Type) where
  constructor MkDepPara
  res : A -> (B -> Type)
  -- f :  -- not clear how to do this yet
