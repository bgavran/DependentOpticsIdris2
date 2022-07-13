module Utils

import Data.DPair

public export
record ExistsFixed {0 type : Type} (this : type -> Type) where
  constructor EvidenceFixed
  0 fst : type
  snd : this fst

public export
data Konst : (0 a : Type) -> (b : a -> Type) -> Type where
  IsKonst : b -> Konst a (\_ => b)
  NotKonst : (0 _ : a) -> (b : a -> Type) -> Konst a b

{-
If this = const t, then require only snd : t, othewrise require 0 fst : type, snd : this fst
