module Para

import DependentLenses

public export
record Para (A, B : Type) (monProd : Type -> Type -> Type) where
  constructor MkPara
  res : Type
  f : monProd res A -> B

-- sigmaPi : {A, B : Type} -> (A -> (B -> Type)) -> Type
-- sigmaPi res = (a : A) -> (b : B ** res a b)

record DepPara (A, B : Cont) where
  constructor MkDepPara
  res : shp A -> shp B -> Type
  
               
--record DepPara (A, B : Type) 
--               (monProd : Type -> Type -> Type) where
--  constructor MkDepPara
--  res : Type -> (Type -> Type) -- it's important that res is private information
--  f : monProd (res A B) A -> B
 
-- fff : {A, B : Type}  -> DepPara A B (,)
-- fff = MkDepPara (\_ => ?r) ?f

-- ParaToDepPara : {A, B : Type} -> (monProd : Type -> Type -> Type) -> Para A B monProd -> DepPara A B monProd
-- ParaToDepPara monProd (MkPara res f) = MkDepPara (\_, _ => res) f
