module CoPara

import Utils
import Data.DPair
import Data.Exists

--------------------------------------------------

public export
record CoPara (A, B : Type) (monProd : Type -> Type -> Type) where
  constructor MkCoPara
  res : Type
  f : A -> monProd B res

public export
graph : (a -> b) -> (a -> (b, a))
graph f a = (f a, a)

graphCoParaCart : {A, B : Type} -> (A -> B) -> CoPara A B (,)
graphCoParaCart f = MkCoPara A (graph f)


--------------------------------------------------
-- Cartesian Dependent CoPara
--------------------------------------------------

public export
sigmaPi : {A, B : Type} -> (A -> (B -> Type)) -> Type
sigmaPi res = (a : A) -> (b : B ** res a b)

public export
record DepCoParaCart (A, B : Type) where
  constructor MkDepCoParaCart
  res : A -> (B -> Type)
  fw : sigmaPi res

public export
CoParaCartToDepCoParaCart : {A, B : Type} -> CoPara A B (,) -> DepCoParaCart A B
CoParaCartToDepCoParaCart (MkCoPara m f) = MkDepCoParaCart
  (\_, _ => m)
  ((\(b, mm) => (b ** mm)) . f)

--------------------------------------------------
-- CoCartesian Dependent CoPara
--------------------------------------------------

public export
sigmaPiCoProd : {A, B : Type} -> (A -> (B -> Type)) -> Type
sigmaPiCoProd res = (a : A) -> Either B (Exists (res a))

public export
record DepCoParaCoCart (A, B : Type) where
  constructor MkDepCoParaCoCart
  res : A -> (B -> Type)
  fw : sigmaPiCoProd res

--------------------------------------------------
-- General Dependent CoPara
--------------------------------------------------

public export
record DepCoPara (A, B : Type) (monProd : Type -> Type -> Type) where
  constructor MkDepCoPara
  res : A -> (B -> Type)
  fw : (a : A) -> monProd B (Exists' B (res a))

--CoParaToDepCoParaAllCart : {A, B : Type} -> CoPara A B (,) -> DepCoPara A B (,)
--CoParaToDepCoParaAllCart (MkCoPara res f) = MkDepCoPara
--  (\_, _ => res)
--  ((\(b, r) => (b, ?fl)) . f)

-- CoParaToDepCoParaAllCoCart : {A, B : Type} -> CoPara A B Either -> DepCoPara A B Either
-- CoParaToDepCoParaAllCoCart (MkCoPara res f) = MkDepCoPara
--    (\_, _ => res)
--    ((\case (Left b) => Left b
--            (Right r) => Right (IsKonst r)) . f)

--------------------------------------------------
-- Composition
--------------------------------------------------

public export
compRes : {A, B, C : Type} -> (A -> (B -> Type)) -> (B -> (C -> Type)) -> (A -> (C -> Type))
compRes r1 r2 = \a, c => (b : B ** (r1 a b, r2 b c))

public export
compRes' : {A, B, C : Type} -> (A -> (B -> Type)) -> (B -> (C -> Type)) -> (A -> (C -> Type))
compRes' r1 r2 = \a, c => (b : B ** Either (r1 a b) (r2 b c))

public export
compDepCoParaCart : {A, B, C : Type} -> DepCoParaCart A B -> DepCoParaCart B C -> DepCoParaCart A C
compDepCoParaCart f g = MkDepCoParaCart
  (compRes (res f) (res g))
  (\a => let (b ** r1) = (fw f) a
             (c ** r2) = (fw g) b
         in (c ** b ** (r1, r2)))
