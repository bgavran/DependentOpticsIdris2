module Church

record Cont where
  constructor MkCont
  shp : Type
  pos : shp -> Type

record OldAction (A, M : Type) where
  constructor MkOldAction
  oldAction : (A, M) -> A

record OldDepAction (A : Type) (M : A -> Type) where
  constructor MkOldDepAction
  olddepaction : (a : A ** M a) -> A


Action : Type
Action = Type -> Type -> Type

DepAction : Type
DepAction = (A : Type) -> (A -> Type) -> Type

Prof : Type
Prof = Type -> Type -> Type

-- generalization of the above where (,) is "act" and -> is "arr"
record Para (act : Action) (arr : Prof) (A, B : Type) where
  constructor MkPara
  P : Type
  action : act A P `arr` B

-- generalization of the above where (,) is "act" and -> is "arr"
record DepPara (depAct : DepAction) (arr : Prof) (A, B : Type) where
  constructor MkDepPara
  P : A -> Type
  action : depAct A P `arr` B

record Optic (act : Type -> Type -> Type) (arr : Type -> Type -> Type) (A, A', B, B' : Type) where
  constructor MkOptic
  res : Type
  fw : A `arr` act B res
  bw : (act res B') `arr` A'


record CoPara (A : Type) (B : Type) (M : A -> Type) where
  constructor MkCoPara
  cpm : (a : A) -> (b : B ** M a)

{-
Let M be a monoidal category.
Let A be a category.
Let a : AxM -> A be an action.
A Para morphism X -> Y where X:A and Y:A is a choice of an object P:M and a morphism a(X, P) -> Y and that's a morphism in A.
-}
