module WeightedCopara

import Cats
import DepAct

public export

public export

CoparaCat : (c : Cat) -> (m : Cat) -> (ac : NonDepAct c m) -> Cat
CoparaCat c m ac = WeightedCoparaCat c m ac (constFunctor ())

CoparaCartesian : Cat
CoparaCartesian = CoparaCat TypeCat TypeCat CartAction

CoparaCoCartesian : Cat
CoparaCoCartesian = CoparaCat TypeCat TypeCat CoCartAction
