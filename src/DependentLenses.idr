module DependentLenses

import CartesianLenses

public export
record Cont where
  constructor MkCont
  shp : Type
  pos : shp -> Type

public export
record DepLens (A, B : Cont) where
  constructor MkDepLens
  fw : shp A -> shp B
  bw : (a : shp A) -> pos B (fw a) -> pos A a


public export
Const : Type -> Type -> Cont
Const ty1 ty2 = MkCont ty1 (const ty2)

CartLensToDepLens : {A, A', B, B' : Type} -> CartLens A A' B B' -> DepLens (Const A A') (Const B B')
CartLensToDepLens (MkCartLens f f') = MkDepLens f (curry f')
