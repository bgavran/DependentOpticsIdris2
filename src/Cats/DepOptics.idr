module Cats.DepOptics


import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.DepCoPara

-- Dependent optics is CoPara of something
-- CoPara(Cont)
public export
DependentOpticsCat : (c : Cat) -> (m : DepAct c) -> (d : IndCat c)
  -> (over : OverDepAct c m d)
  -> Cat
DependentOpticsCat c m d over = DepCoparaCat (FLens c d) (GrothAct c m d over)

public export
CartDepOptic : Cat
CartDepOptic = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct

public export
DepLensToDepOptic : (arr DLens) (MkGrothObj a a') (MkGrothObj b b') -> (arr CartDepOptic) (MkGrothObj a a') (MkGrothObj b b')
DepLensToDepOptic (MkGrothMor f f') = MkDepCoparaMor
  (\_ => Bool)
  (MkGrothMor (\a => ?ff) ?bw)
  
