module Cats.ChurchForRealz

import Data.DPair
import Erased
import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.DepCoPara
import Cats.DepOptics

embedCartLensFLens : (a -> b) -> (a -> b' -> a') -> (arr DLens) (MkGrothObj a (\_ => a')) (MkGrothObj b (\_ => b'))
embedCartLensFLens f f' = MkGrothMor f f'


-- objects of Fam(Set) are containers
Cont : Type
Cont = GrothObj TypeCat (fibOp TypeCat FamInd)

Cont0 : Type
Cont0 = GrothObj TypeCat (fibOp TypeCat Fam0Ind)

-- using FamInd twice below!
CartDepOptics : Cat
CartDepOptics = DependentOpticsCat TypeCat DepCartAction FamInd CospanOverAct

CartDepOptics0 : Cat
CartDepOptics0 = DependentOpticsCat TypeCat CartAction Fam0Ind Cospan0OverAct
