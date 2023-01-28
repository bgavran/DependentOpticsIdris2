module Cats.ChurchForRealz

import Data.DPair
import Erased
import Cats.Cats
import Cats.Groth
import Cats.DepAct
import Cats.DepCoPara
import Cats.DepOptics


-- objects of Fam(Set) are containers
Cont : Type
Cont = GrothObj TypeCat (fibOp TypeCat FamInd)

Cont0 : Type
Cont0 = GrothObj TypeCat (fibOp TypeCat Fam0Ind)
