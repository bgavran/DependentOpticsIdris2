module Data.Exists

import Data.DPair

public export
data Exists' : (ty : Type) -> (d : ty -> Type) -> Type where
  Ev : ((x : ty) -> (e : Exists d ** e.fst = x)) -> Exists' ty d
