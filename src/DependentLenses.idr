module DependentLenses

import CartesianLenses
import Coproduct

public export
record Cont where
  constructor MkCont
  shp : Type
  pos : shp -> Type

public export
record DepLens (a, b : Cont) where
  constructor MkDepLens
  fw : a.shp -> b.shp
  bw : (x : a.shp) -> b.pos (fw x) -> a.pos x

public export
Const : Type -> Type -> Cont
Const ty1 ty2 = MkCont ty1 (const ty2)

CartLensToDepLens : {A, A', B, B' : Type} -> CartLens A A' B B' -> DepLens (Const A A') (Const B B')
CartLensToDepLens (MkCartLens f f') = MkDepLens f (curry f')

public export
record ClosedDepLens (A, B : Cont) where
  constructor MkClosedDepLens
  f : (a : shp A) -> (b : shp B ** pos B b -> pos A a)

public export
coproduct : Cont -> Cont -> Cont
coproduct cont1 cont2 = MkCont
  ((shp cont1) + (shp cont2))
  (elim cont1.pos cont2.pos)

coproductMap : {A, B, Z : Cont} -> DepLens A Z -> DepLens B Z -> DepLens (coproduct A B) Z
coproductMap (MkDepLens f f') (MkDepLens g g') = MkDepLens
  (\ab => case ab of
    L a => f a
    R b => g b)
  (\ab => case ab of
    L a => f' a
    R b => g' b)
