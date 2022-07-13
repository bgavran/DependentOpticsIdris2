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

public export
record ClosedDepLens (A, B : Cont) where
  constructor MkClosedDepLens
  f : (a : shp A) -> (b : shp B ** pos B b -> pos A a)

public export
data CoProduct ty1 ty2 = L ty1 | R ty2

copr : Type -> Type -> Bool -> Type
copr ty1 ty2 False = ty1
copr ty1 ty2 True = ty2

-- copr' : (ty1, ty2 : Type) -> (b : Bool ** copr ty1 ty2 b)
-- copr' = ?ll

public export
coproductPair : (a -> c) -> (b -> d) -> CoProduct a b -> CoProduct c d
coproductPair f g (L l) = L (f l)
coproductPair f g (R r) = R (g r)

public export
elim : (a -> c) -> (b -> c) -> CoProduct a b -> c
elim f g (L x) = f x
elim f g (R x) = g x

public export
elim' : {0 c : a -> Type} -> {0 d : b -> Type} ->
        (f : (x : a) -> c x) -> (g : (x : b) -> d x) -> (p : CoProduct a b) -> (DependentLenses.elim c d p)
elim' f g (L x) = f x
elim' f g (R x) = g x

public export
coproductCont : Cont -> Cont -> Cont
coproductCont cont1 cont2 = MkCont
  (CoProduct cont1.shp cont2.shp)
  (elim cont1.pos cont2.pos)

coproductMap : {A, B, Z : Cont} -> DepLens A Z -> DepLens B Z -> DepLens (coproductCont A B) Z
coproductMap (MkDepLens f f') (MkDepLens g g') = MkDepLens
  (\ab => case ab of
    L a => f a
    R b => g b)
  (\ab => case ab of
    L a => f' a
    R b => g' b)
