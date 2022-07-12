module Data.Container

import Data.Coproduct

public export
record Cont where
  constructor MkCont
  shp : Type
  pos : shp -> Type

public export
Const : Type -> Type -> Cont
Const ty1 ty2 = MkCont ty1 (const ty2)

public export
coproduct : Cont -> Cont -> Cont
coproduct cont1 cont2 = MkCont
  (shp cont1 + shp cont2)
  (elim cont1.pos cont2.pos)

public export
product : Cont -> Cont -> Cont
product cont1 cont2 = MkCont
  (shp cont1, shp cont2)
  (\x => cont1.pos (fst x) + cont2.pos (snd x))

public export
tensor : Cont -> Cont -> Cont
tensor cont1 cont2 = MkCont
  (shp cont1, shp cont2)
  (\x => (cont1.pos (fst x), cont2.pos (snd x)))
