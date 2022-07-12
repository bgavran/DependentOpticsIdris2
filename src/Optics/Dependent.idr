module Optics.Dependent

import Optics.Plain
import Data.Coproduct
import Data.Container
import Lens.Dependent
import Optics
import CoPara
import Data.DPair
import Data.Product

public export
record DepOptic (a, b : Cont) where
  constructor MkDepOptic
  fw : a.shp -> b.shp
  0 res : a.shp -> b.shp -> Type
  bw : {0 x : a.shp} -> {0 y : b.shp} -> res x y -> b.pos y -> a.pos x

embedIntoDepOptics : DepLens a b -> DepOptic a b
embedIntoDepOptics ls = MkDepOptic
  (fw ls)
  (\x, y => (aRes : a.shp ** (aRes = x, fw ls x = y)))
  (\(k ** (p1, p2)), y => let v = ls.bw k (rewrite p1 in rewrite p2 in y) in rewrite sym p1 in v)

compDepOptic : {a, b, c : Cont} -> DepOptic a b -> DepOptic b c -> DepOptic a c
compDepOptic f g = MkDepOptic
  (g.fw . f.fw)
  (\x, y => (v : b.shp ** (f.res x v, g.res v y)))
  (\(x ** (p1, p2)), y => f.bw p1 (g.bw p2 y))

record DepPrisms (a, b : Cont) where
  constructor MkDepPrism
  0 r : a.shp -> Type
  0 r' : (x : a.shp) -> r x -> Type
  fw : (x : a.shp) -> (choice : Bool ** Choice choice (r x) b.shp)
  bw : {0 x : a.shp} -> (choice : Bool) -> {0 pick : Choice choice (r x) b.shp} ->
       Elim (r' x) b.pos choice pick -> a.pos x

mapElim : {y : _} -> elim (\_ => c) (\_ => d) y -> c + d
mapElim x {y = (L y)} = L x
mapElim x {y = (R y)} = R x

0 collapseElim : {0 y : _ } -> elim (\_ => a) (\_ => a) y = a
collapseElim {y = (L x)} = Refl
collapseElim {y = (R x)} = Refl

elimBimap : {y : _} ->
            (r -> p) -> (s -> q) -> elim (\_ => r) (\_ => s) y -> elim (\_ => p) (\_ => q) y
elimBimap f g x {y = (L y)} = f x
elimBimap f g x {y = (R y)} = g x

0 elimBoth : {0 y : _} ->
             elim (\_ => r) (\_ => s) y = elim (\_ => p) (\_ => q) y

-- Prisms embed into dependent prisms
embedPrisms : PlainOptics (+) a b -> DepPrisms (MkCont (fst a) (const (snd a)))
                                               (MkCont (fst b) (const (snd b)))
embedPrisms (MkPlainOptic r fw bw) = MkDepPrism
  (const r)
  (const (const r))
  (toChoice . fw)
  (\case True => bw . L
         False => bw . R)

composeDepPrisms : DepPrisms a b -> DepPrisms b c -> DepPrisms a c
composeDepPrisms (MkDepPrism r1 r1' fw1 bw1) (MkDepPrism r2 r2' fw2 bw2) = MkDepPrism
  -- The composition of two dependent prisms has a coproduct as residual
  -- indicating which residual was taken, L if it comes from the first
  -- prism, R if it comes from the second prism
  (\x => r1 x + Exists r2)
  -- (\x => elim (r1' x) (\(Evidence a b) => r2' a b))
  (\x => \y => r1' x ?ss + ?w)--elim (r1' x) (\(Evidence a b) => r2' a b))
  -- Attempt the forward part of the first lens
  (\x => case fw1 x of
      -- if we succeed and get a value of type `b.shp` then we apply it to the fw
      -- of the second lens
      (False ** bVal) => case fw2 bVal of
          -- If the second lens succeeds we return a value of type `c.shp`
          ((False ** cVal)) => (False ** cVal)
          -- Otherwise we return a residual of type `Exists r2`
          ((True ** residual)) => (True ** R (Evidence bVal residual))
      -- If the first lens fails we return its residual
      (True ** residual) => (True ** L residual))
  (\case True => \x => ?qwqe2
         False => \cVal => bw1 False (bw2 False cVal))

record GenOptics
  (Rel : Type -> Type -> Type)
  (El : {a, b : Type} -> (a -> Type) -> (b -> Type) -> Rel a b -> Type)
  (a, b : Cont) where
  constructor MkGen
  0 r : a.shp -> Type
  0 r' : (x : a.shp) -> r x -> Type
  fw : (x : a.shp) -> (b.shp `Rel` r x)
  bw : {0 x : a.shp} -> {0 y : b.shp `Rel` r x} -> El b.pos (r' x) y -> a.pos x

CoSum : (a -> Type) -> (b -> Type) -> (a, b) -> Type
CoSum f g x = Pair (f (fst x)) (g (snd x))

embedDLens : DepOptic a b -> GenOptics Prelude.const (\f, g, x => f x) a b
embedDLens (MkDepOptic fw res bw) = MkGen
  (\x => b.shp)
  (\x, y => (v : a.shp ** (v = x, fw x = y)))
  (\x => fw x)
  (\x => ?bwww)

composeGen : {rel : Type -> Type -> Type} -> {e : {a, b, c : Type} -> (a -> c) -> (b -> c) -> rel a b -> c} ->
             GenOptics rel e a b -> GenOptics rel e b c -> GenOptics rel e a c


{-
----------------------------------------
-- Embeddings of other kinds of lenses/optics into dependent optics
----------------------------------------
DepLensToDepOptic : {A, B : Cont} -> DepLens A B -> DepOptic A B
DepLensToDepOptic (MkDepLens f f') = MkDepOptic
  (MkDepCoPara
    (\a, b => (aRes : shp A ** (a = aRes, b = f a))) (\a => (f a ** a  ** (Refl, Refl))))
  (\(aRes ** (p, q)) => rewrite q in rewrite p in f' aRes)

OpticToDepOptic : {A, A', B, B' : Type} -> Optic A A' B B' -> DepOptic (Const A A') (Const B B')
OpticToDepOptic (MkOptic res f f') = MkDepOptic
  (CoParaToDepCoPara (MkCoPara res f))
  (curry f')

ClosedDepLensToDepOptic : {A, B : Cont} -> ClosedDepLens A B -> DepOptic A B
ClosedDepLensToDepOptic (MkClosedDepLens f) = MkDepOptic
  (MkDepCoPara (\a, b => pos B b -> pos A a) f)
  (\f', b' => f' b')

----------------------------------------

lemma : (A, B, Z : Cont) ->
        (res1 : (A .shp -> Z .shp -> Type)) ->
        ((a : A .shp) -> (b : Z .shp ** res1 a b)) ->
        ((a : A .shp) -> (b : Z .shp) -> res1 a b -> Z .pos b -> A .pos a) ->
        (res2 : (B .shp -> Z .shp -> Type)) ->
        ((a : B .shp) -> (b : Z .shp ** res2 a b)) ->
        ((a : B .shp) -> (b : Z .shp) -> res2 a b -> Z .pos b -> B .pos a) ->
        (0 a : CoProduct (shp A) (shp B)) -> (0 b : shp Z) ->
        elim res1 res2 a b -> Z .pos b -> elim (A .pos) (B .pos) a
lemma c1 c2 c3 res1 f g res2 f1 g1 a b x y =
  let
      v = elim' {c = c1.pos} {d = c2.pos} (\w => ?dd) ?bb in ?lemma_rhs

coproductMap : {A, B, Z : Cont} -> DepOptic A Z -> DepOptic B Z -> DepOptic (coproduct A B) Z
coproductMap (MkDepOptic (MkDepCoPara res1 fw1) bw1) (MkDepOptic (MkDepCoPara res2 fw2) f2) = MkDepOptic
  (MkDepCoPara (elim res1 res2) (\case L x => fw1 x
                                       R x => fw2 x))
  (lemma A B Z res1 fw1 (\_,_ => bw1) res2 fw2 (\_, _ => f2) _ _)
