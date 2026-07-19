{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Sketch: the category Poly.
--
-- Polynomial objects are syntactic expressions, promoted to a kind:
--
--     p, q ::= Y              the identity polynomial
--           |  Const A        a constant set
--           |  Exp A          y^A
--           |  Sum p q        coproduct
--           |  Prod p q       cartesian product
--           |  Tensor p q     Dirichlet/parallel product
--           |  Comp p q       composition (substitution)
--
-- The kind @Poly@ is promoted, so polynomial expressions live at the type
-- level.  'Eval' is a GADT that witnesses the value shape of @p(x)@.  We use
-- a GADT rather than a type family because 'Eval' is not injective in @x@;
-- the GADT lets GHC keep track of the evaluation variable without ambiguity.
--
-- Morphisms are natural transformations between the induced polynomial
-- functors, equivalently bundle maps (positions forward, directions
-- backward).
--
-- Two extra constructors make dependent lenses expressible:
--
-- * 'Konst' introduces a global element (a constant position).
-- * 'Depend' is the copower universal property: a @Const a@-indexed family
--   of morphisms @p -> q@.
--
-- With them, the general point-dependent lens @(get :: a -> b, put :: a -> db -> da)@
-- is a two-line 'Morphism'.
--
-- The 'Tensor' constructor adds the Dirichlet (parallel) product. It requires
-- 'Pos' and 'Dir' type families because a value of @(p ⊗ q)(x)@ is a pair of
-- positions together with a single function out of the product of direction
-- sets — not derivable from a pair of ordinary 'Eval' values.
module Circuit.Poly
  ( -- * Polynomial expressions
    Poly (..),
    Eval (..),

    -- * Positions and directions
    Pos,
    Dir,

    -- * Netlist view
    Netlist (..),
    netRoundTrip,
    tensorUnitorL,
    tensorUnitorL',
    tensorUnitorR,
    tensorUnitorR',

    -- * Tensor functoriality
    morphAt,
    parT,

    -- * Composition product
    nestedToComp,
    compToNested,

    -- * Tensor wiring
    tensorEval,
    parWiring,

    -- * Morphisms
    Morphism (..),
    runMorphism,

    -- * Lenses
    Mono,
    lens,
    dagger,
    applyLens,

    -- * Dynamical systems
    System,
    step,
  )
where

import Circuit.Classes (Category (..), Discrete (..), (>>>))
import Data.Bifunctor
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Poly
-- >>> import Prelude hiding (id, (.))

-- | Syntactic polynomial objects, promoted to a kind.
data Poly
  = Y
  | Const Type
  | Exp Type
  | Sum Poly Poly
  | Prod Poly Poly
  | Tensor Poly Poly
  | Comp Poly Poly

-- | Position set of a polynomial.
--
-- For a value of @p(x)@, 'Pos p' is the index type of positions.
type family Pos (p :: Poly) :: Type where
  Pos 'Y = ()
  Pos ('Const a) = a
  Pos ('Exp a) = ()
  Pos ('Sum p q) = Either (Pos p) (Pos q)
  Pos ('Prod p q) = (Pos p, Pos q)
  Pos ('Tensor p q) = (Pos p, Pos q)
  Pos ('Comp p q) = (Pos p, Dir p -> Pos q)

-- | Direction set of a polynomial.
--
-- For a value of @p(x)@ at a given position, 'Dir p' is the domain of the
-- function into @x@.
--
-- There is no 'Dir ('Sum p q)' row: directions over a sum are
-- position-dependent. At 'Left i' the direction set is 'Dir p'; at 'Right j'
-- it is 'Dir q'. The 'ES' constructor records this correctly; a flattened
-- family would over-approximate and make 'ET' over a sum-containing tensor
-- unsound. This is the known representation fork: a position-indexed 'Dir'
-- family would be fully general, but is not needed for the monomial / wiring
-- fragment this package targets first.
--
-- For 'Comp', @'Dir' ('Comp p q) = ('Dir p, 'Dir q)@ is the same flat
-- approximation: the @q@-position (hence its honest pin set) depends on which
-- @p@-direction was taken.  Exact for Sum-free factors with uniform
-- directions — the monomial fragment.  See 'loom/circuits-monomial.md'.
type family Dir (p :: Poly) :: Type where
  Dir 'Y = ()
  Dir ('Const a) = Void
  Dir ('Exp a) = a
  Dir ('Prod p q) = Either (Dir p) (Dir q)
  Dir ('Tensor p q) = (Dir p, Dir q)
  Dir ('Comp p q) = (Dir p, Dir q)

-- | Values of a polynomial functor @p@ evaluated at @x@.
--
-- The constructors mirror the polynomial grammar.  'EP' and 'ES' wrap the
-- standard product and coproduct of Haskell ('(,)' and 'Either'); they are
-- not reimplemented, only tagged so that the polynomial shape remains
-- inspectable.
--
-- 'ET' is the Dirichlet tensor: a pair of positions with one function out of
-- the product of direction sets. This cannot be built from a pair of ordinary
-- 'Eval' values, which is why 'Pos' and 'Dir' are needed.
--
-- 'EC' is the composition product: a @p@-position with a @q@-component hung on
-- each @p@-pin, and a path @(dp, dq)@ into @x@.
data Eval (p :: Poly) (x :: Type) where
  EY :: x -> Eval 'Y x
  EK :: c -> Eval ('Const c) x
  EE :: (a -> x) -> Eval ('Exp a) x
  ES :: Either (Eval p x) (Eval q x) -> Eval ('Sum p q) x
  EP :: (Eval p x, Eval q x) -> Eval ('Prod p q) x
  ET :: (Pos p, Pos q) -> ((Dir p, Dir q) -> x) -> Eval ('Tensor p q) x
  EC ::
    (Pos p, Dir p -> Pos q) ->
    ((Dir p, Dir q) -> x) ->
    Eval ('Comp p q) x

instance Functor (Eval p) where
  fmap f = \case
    EY x -> EY (f x)
    EK c -> EK c
    EE g -> EE (f . g)
    ES e -> ES (bimap (fmap f) (fmap f) e)
    EP (a, b) -> EP (fmap f a, fmap f b)
    ET pos g -> ET pos (f . g)
    EC pos g -> EC pos (f . g)

-- ** Netlist view

-- | Polynomials that admit a netlist view: every value is a chosen position
-- together with an assignment of that position's pins (directions) into @x@.
--
-- The view is defined structurally over the promoted grammar. It is the
-- missing inverse that lets us build arbitrary 'Eval' values from netlist
-- data — in particular it underlies the unitors for the Dirichlet tensor
-- and the functorial action @parT@ on tensor factors.
--
-- 'Sum' is deliberately /not/ an instance. A sum value stores its pin set
-- in the branch constructor ('ES'), so there is no single flat direction
-- set 'Dir' can assign to it. That is the honest boundary of the view;
-- handling sums position-dependently needs the full position-indexed
-- representation fork (see the 'Dir' haddock and 'loom/circuits-monomial.md').
class Netlist (p :: Poly) where
  -- | Extract the position and pin assignment from a polynomial value.
  toNet :: Eval p x -> (Pos p, Dir p -> x)

  -- | Build a polynomial value from a position and pin assignment.
  fromNet :: Pos p -> (Dir p -> x) -> Eval p x

instance Netlist 'Y where
  toNet (EY x) = ((), \() -> x)
  fromNet () k = EY (k ())

instance Netlist ('Const a) where
  toNet (EK c) = (c, absurd)
  fromNet c _ = EK c

instance Netlist ('Exp a) where
  toNet (EE f) = ((), f)
  fromNet () = EE

instance (Netlist p, Netlist q) => Netlist ('Prod p q) where
  toNet (EP (u, v)) =
    let (i, f) = toNet u
        (j, g) = toNet v
     in ((i, j), either f g)
  fromNet (i, j) k = EP (fromNet i (k . Left), fromNet j (k . Right))

instance Netlist ('Tensor p q) where
  toNet (ET ij f) = (ij, f)
  fromNet = ET

instance Netlist ('Comp p q) where
  toNet (EC i k) = (i, k)
  fromNet = EC

-- | Reassemble a value after taking it apart. This is the executable form
-- of the round-trip law @'fromNet' ('toNet' v) ≡ v@.
netRoundTrip :: (Netlist p) => Eval p x -> Eval p x
netRoundTrip v = uncurry fromNet (toNet v)

-- | Left unitor for the Dirichlet tensor: @Y ⊗ p ≅ p@.
--
-- The @Y@ factor is degenerate; collapse via 'fromNet' on the other factor.
tensorUnitorL :: (Netlist p) => Eval ('Tensor 'Y p) x -> Eval p x
tensorUnitorL (ET ((), i) f) = fromNet i (\dp -> f ((), dp))

-- | Inverse left unitor: @p -> Y ⊗ p@.
tensorUnitorL' :: (Netlist p) => Eval p x -> Eval ('Tensor 'Y p) x
tensorUnitorL' v =
  let (i, k) = toNet v
   in ET ((), i) (\((), dp) -> k dp)

-- | Right unitor for the Dirichlet tensor: @p ⊗ Y ≅ p@.
tensorUnitorR :: (Netlist p) => Eval ('Tensor p 'Y) x -> Eval p x
tensorUnitorR (ET (i, ()) f) = fromNet i (\dp -> f (dp, ()))

-- | Inverse right unitor: @p -> p ⊗ Y@.
tensorUnitorR' :: (Netlist p) => Eval p x -> Eval ('Tensor p 'Y) x
tensorUnitorR' v =
  let (i, k) = toNet v
   in ET (i, ()) (\(dp, ()) -> k dp)

-- | Read the bundle map off a 'Morphism' at a chosen position.
--
-- Instantiating the output as @'Dir' p@ turns an opaque morphism into a
-- forward position plus a backward direction map — the crux that makes
-- 'parT' a few lines.
morphAt :: (Netlist p, Netlist p') => Morphism p p' -> Pos p -> (Pos p', Dir p' -> Dir p)
morphAt m i =
  let (i', k) = toNet (runMorphism m (fromNet i id))
   in (i', k)

-- | Functorial action of the Dirichlet tensor on 'Netlist' factors.
--
-- Map each tensor factor through its morphism independently; backward
-- directions thread through both pullback maps.
parT ::
  (Netlist p, Netlist q, Netlist p', Netlist q') =>
  Morphism p p' ->
  Morphism q q' ->
  Eval ('Tensor p q) x ->
  Eval ('Tensor p' q') x
parT m n (ET (i, j) f) =
  let (i', pullM) = morphAt m i
      (j', pullN) = morphAt n j
   in ET (i', j') (f . bimap pullM pullN)

-- | Composition-product view of a nested evaluation @'Eval' p ('Eval' q x)@.
--
-- Correctness iso (right): @'Eval' ('Comp' p q) x ≅ 'Eval' p ('Eval' q x)@.
nestedToComp :: (Netlist p, Netlist q) => Eval p (Eval q x) -> Eval ('Comp p q) x
nestedToComp v =
  let (i, g) = toNet v
   in EC (i, fst . toNet . g) (\(dp, dq) -> snd (toNet (g dp)) dq)

-- | Nested evaluation from a composition-product value.
--
-- Correctness iso (left): inverse of 'nestedToComp'.
compToNested :: (Netlist p, Netlist q) => Eval ('Comp p q) x -> Eval p (Eval q x)
compToNested (EC (i, hang) k) =
  fromNet i (\dp -> fromNet (hang dp) (\dq -> k (dp, dq)))

-- | Pair two polynomial values into a Dirichlet tensor (@p ⊗ q@).
--
-- Each factor contributes its position and pin assignment; the result is
-- one joint assignment over the product of direction sets.
tensorEval :: (Netlist p, Netlist q) => Eval p a -> Eval q b -> Eval (Tensor p q) (a, b)
tensorEval v w =
  let (i, fv) = toNet v
      (j, fw) = toNet w
   in ET (i, j) (bimap fv fw)

-- | Place two Moore systems side by side: interface @p ⊗ q@, state @(s, t)@.
--
-- This is the entry point for acyclic wiring over the Dirichlet tensor —
-- boxes in parallel, pins assigned jointly.
parWiring :: (Netlist p, Netlist q) => System s p -> System t q -> System (s, t) (Tensor p q)
parWiring sp sq (s, t) = tensorEval (sp s) (sq t)

-- $netlist-roundtrip
--
-- Round trips hold for the structural instances. The witnesses below are
-- chosen so that a placeholder 'fromNet'/'toNet' that ignores its input
-- would fail: they use non-identity pin assignments and non-unit direction
-- sets.
--
-- 'Y': the pin assignment is nondegenerate because it must return the stored
-- value.
--
-- >>> let yv = EY 'a' :: Eval 'Y Char
-- >>> case netRoundTrip yv of EY c -> c
-- 'a'
--
-- 'Const': the direction set is 'Void', so the assignment is unique.
--
-- >>> let cv = EK True :: Eval ('Const Bool) Bool
-- >>> case netRoundTrip cv of EK b -> b
-- True
--
-- 'Exp': round-trip holds pointwise on the direction set.
--
-- >>> let ev = EE (\case 'a' -> 1; 'b' -> 2; _ -> 3) :: Eval ('Exp Char) Int
-- >>> case netRoundTrip ev of EE f -> (f 'a', f 'b', f 'c')
-- (1,2,3)
--
-- 'Prod': directions split over 'Either'; the witness uses different
-- behaviour on each side. Both factors here are 'Exp Char' so a mutant that
-- sends both sides through 'Left' still compiles but produces the wrong value
-- on the right.
--
-- >>> let pv = EP (EE (\c -> c : "!"), EE (\c -> c : "?")) :: Eval ('Prod ('Exp Char) ('Exp Char)) String
-- >>> case netRoundTrip pv of EP (EE f, EE g) -> (f 'x', g 'y')
-- ("x!","y?")
--
-- 'Tensor': the constructor already /is/ netlist form, but the witness
-- still exercises the split product of directions.
--
-- >>> let tv = ET ((), ()) (\(d1, d2) -> d1 ++ d2) :: Eval ('Tensor ('Exp String) ('Exp String)) String
-- >>> case netRoundTrip tv of ET ((), ()) f -> f ("hello ", "world")
-- "hello world"
--
-- The position-round-trip law @toNet ('fromNet' i k) == (i, k)@ also holds
-- pointwise. For 'Prod' this is where a broken split would show up.
--
-- >>> let (i, k) = toNet (fromNet ((), ()) (\case Left c -> c : "!"; Right b -> if b then "yes" else "no") :: Eval ('Prod ('Exp Char) ('Exp Bool)) String)
-- >>> (i, k (Left 'x'), k (Right False))
-- (((),()),"x!","no")
--
-- Left unitor: @Y ⊗ Mono@ collapses to @Mono@ and back.  Pin assignment
-- transforms (@dn -> show dn ++ "!"@) — a stub that ignores @f@ fails.
--
-- >>> let yt = ET ((), (5, ())) (\((), Right dn) -> show dn ++ "!") :: Eval ('Tensor 'Y (Mono Int Int)) String
-- >>> case tensorUnitorL yt of EP (EK n, EE f) -> (n, f 7, f 42)
-- (5,"7!","42!")
--
-- >>> let mono = EP (EK 5, EE (\dn -> show dn ++ "!")) :: Eval (Mono Int Int) String
-- >>> case tensorUnitorL' mono of ET ((), (n, ())) f -> (n, f ((), Right 7))
-- (5,"7!")
--
-- >>> case tensorUnitorL (tensorUnitorL' mono) of EP (EK n, EE f) -> (n, f 3)
-- (5,"3!")
--
-- Right unitor: position pair @(i, ())@ not @(() , i)@.
--
-- >>> let ty = ET ((5, ()), ()) (\(Right dn, ()) -> dn + 10) :: Eval ('Tensor (Mono Int Int) 'Y) Int
-- >>> case tensorUnitorR ty of EP (EK n, EE f) -> (n, f 3, f 7)
-- (5,13,17)
--
-- >>> let monoInt = EP (EK 5, EE (\dn -> dn + 1)) :: Eval (Mono Int Int) Int
-- >>> case tensorUnitorR (tensorUnitorR' monoInt) of EP (EK n, EE f) -> (n, f 3)
-- (5,4)

-- | A morphism @p -> q@ in Poly, encoded as a natural transformation
-- between the evaluated functors.
--
-- By the Yoneda / sigma universal property, this is equivalent to a
-- bundle map: a function on positions together with a contravariant
-- family of functions on directions.
--
-- 'Konst' and 'Depend' extend the original Poly sketch so that backward
-- maps can depend on the current position, giving point-dependent lenses.
data Morphism (p :: Poly) (q :: Poly) where
  -- | Identity morphism.
  Id :: Morphism p p
  -- | Covariant embedding of a plain function into constants.
  ConstMap :: (a -> b) -> Morphism ('Const a) ('Const b)
  -- | Contravariant embedding of a plain function into exponentials.
  ExpMap :: (a -> b) -> Morphism ('Exp b) ('Exp a)
  -- | Sequential composition.
  Compose :: Morphism q r -> Morphism p q -> Morphism p r
  -- | Parallel composition (cartesian product of morphisms).
  Par :: Morphism p p' -> Morphism q q' -> Morphism ('Prod p q) ('Prod p' q')
  -- | Coproduct injections.
  Inl :: Morphism p ('Sum p q)
  Inr :: Morphism q ('Sum p q)
  -- | Coproduct case analysis.
  Case :: Morphism p r -> Morphism q r -> Morphism ('Sum p q) r
  -- | Product projections.
  Fst :: Morphism ('Prod p q) p
  Snd :: Morphism ('Prod p q) q
  -- | Product pairing.
  Pair :: Morphism r p -> Morphism r q -> Morphism r ('Prod p q)
  -- | Global element (constant introduction).
  Konst :: b -> Morphism p ('Const b)
  -- | Copower universal property: a @Const a@-indexed family of morphisms.
  Depend :: (a -> Morphism p q) -> Morphism ('Prod ('Const a) p) q
  -- | Left associator for the Dirichlet tensor:
  -- @((p ⊗ q) ⊗ r) -> (p ⊗ (q ⊗ r))@.
  TensorAssocL :: Morphism ('Tensor ('Tensor p q) r) ('Tensor p ('Tensor q r))
  -- | Right associator for the Dirichlet tensor.
  TensorAssocR :: Morphism ('Tensor p ('Tensor q r)) ('Tensor ('Tensor p q) r)
  -- | Symmetry/braiding for the Dirichlet tensor: @p ⊗ q -> q ⊗ p@.
  TensorBraid :: Morphism ('Tensor p q) ('Tensor q p)
  -- | Functorial action of the Dirichlet tensor on monomial morphisms:
  -- @f ⊗ g : (a·y^{da}) ⊗ (c·y^{dc}) -> (b·y^{db}) ⊗ (d·y^{dd})@.
  --
  -- Restricted to monomials because the current 'Dir' family cannot express
  -- position-dependent direction sets (in particular, 'Sum' has no 'Dir' row).
  ParT ::
    Morphism (Mono a da) (Mono b db) ->
    Morphism (Mono c dc) (Mono d dd) ->
    Morphism ('Tensor (Mono a da) (Mono c dc)) ('Tensor (Mono b db) (Mono d dd))

instance Category Morphism where
  type Ob Morphism a = ()
  id = Id
  (.) = Compose

-- | Interpret a 'Morphism' as a natural transformation.
runMorphism :: Morphism p q -> (forall x. Eval p x -> Eval q x)
runMorphism = \case
  Id -> id
  ConstMap f -> \(EK a) -> EK (f a)
  ExpMap f -> \(EE g) -> EE (g . f)
  Compose g f -> runMorphism g . runMorphism f
  Par f g -> \(EP (a, b)) -> EP (runMorphism f a, runMorphism g b)
  Inl -> ES . Left
  Inr -> ES . Right
  Case f g -> \case
    ES (Left a) -> runMorphism f a
    ES (Right b) -> runMorphism g b
  Fst -> \(EP (a, _)) -> a
  Snd -> \(EP (_, b)) -> b
  Pair f g -> \r -> EP (runMorphism f r, runMorphism g r)
  Konst b -> \_ -> EK b
  Depend k -> \(EP (EK a, p)) -> runMorphism (k a) p
  TensorAssocL -> \(ET ((pp, pq), pr) f) ->
    ET (pp, (pq, pr)) (f . (\(dp, (dq, dr)) -> ((dp, dq), dr)))
  TensorAssocR -> \(ET (pp, (pq, pr)) f) ->
    ET ((pp, pq), pr) (f . (\((dp, dq), dr) -> (dp, (dq, dr))))
  TensorBraid -> \(ET (pp, pq) f) ->
    ET (pq, pp) (f . (\(dq, dp) -> (dp, dq)))
  ParT m n -> parT m n

-- ** Dirichlet tensor

-- | The Dirichlet tensor @p ⊗ q@ pairs positions and multiplies directions.
-- A value is a position pair together with one function out of the product of
-- direction sets — not two separate functions.
--
-- >>> let ab = ET ((), ()) (\(a, b) -> a ++ b) :: Eval ('Tensor ('Exp String) ('Exp String)) String
-- >>> case ab of ET ((), ()) f -> f ("hello ", "world")
-- "hello world"
--
-- 'fmap' acts on the result of the combined direction function.
--
-- >>> let v = ET ((), ()) (\(a, b) -> a + b) :: Eval ('Tensor ('Exp Int) ('Exp Int)) Int
-- >>> case fmap (* 2) v of ET ((), ()) f -> f (3, 4)
-- 14
--
-- The braiding swaps both the position pair and the direction pair.
--
-- >>> case runMorphism TensorBraid ab of ET ((), ()) f -> f ("world", "hello ")
-- "hello world"
--
-- The associator reassociates both positions and directions.
--
-- >>> let abc = ET (((), ()), ()) (\((a, b), c) -> a ++ b ++ c) :: Eval ('Tensor ('Tensor ('Exp String) ('Exp String)) ('Exp String)) String
-- >>> case runMorphism TensorAssocL abc of ET ((), ((), ())) f -> f ("a", ("b", "c"))
-- "abc"
-- >>> case runMorphism TensorAssocR (runMorphism TensorAssocL abc) of ET (((), ()), ()) f -> f (("x", "y"), "z")
-- "xyz"
--
-- 'ParT' is the functorial action of tensor on monomials: map each factor
-- independently, backward directions thread through both.
--
-- The puts are deliberately non-identity: a test with identity puts would still
-- pass if ParT ignored the factor morphisms and threaded directions straight
-- through (the mutation-review catch).
--
-- >>> let m1 = lens show (\n dn -> n + dn) :: Morphism (Mono Int Int) (Mono String Int)
-- >>> let m2 = lens (\b -> if b then 1 else 0 :: Int) (\b db -> b && db) :: Morphism (Mono Bool Bool) (Mono Int Bool)
-- >>> let v = ET ((5, ()), (True, ())) (\(Right n, Right b) -> (n, b)) :: Eval ('Tensor (Mono Int Int) (Mono Bool Bool)) (Int, Bool)
-- >>> case runMorphism (ParT m1 m2) v of ET ((_, ()), (_, ())) f -> f (Right 3, Right True)
-- (8,True)
-- >>> case runMorphism (ParT m1 m2) v of ET ((_, ()), (_, ())) f -> f (Right 2, Right False)
-- (7,False)
--
-- 'parT' on non-monomial 'Netlist' factors ('Exp' morphisms via 'ExpMap').
-- Both pullbacks must fire; dropping either factor leaves the wrong sign.
--
-- >>> let v = ET ((), ()) (\(i, b) -> if b then i else -i) :: Eval ('Tensor ('Exp Int) ('Exp Bool)) Int
-- >>> let m = ExpMap (+ 10) :: Morphism ('Exp Int) ('Exp Int)
-- >>> let n = ExpMap not :: Morphism ('Exp Bool) ('Exp Bool)
-- >>> case parT m n v of ET ((), ()) g -> (g (3, True), g (0, False))
-- (-13,10)
--
-- >>> case parT m n v of ET ((), ()) g -> g (3, True)
-- -13

-- ** Composition product

--
-- Correctness iso @'Eval' ('Comp' p q) x ≅ 'Eval' p ('Eval' q x)@.  The
-- @hang@ map must depend on the outer @p@-direction — a constant hang fails.
--
-- >>> let nested = EP (EK 5, EE (\dn -> EP (EK (show dn ++ "!"), EE (\c -> [c] ++ "?")))) :: Eval (Mono Int Int) (Eval (Mono String Char) String)
-- >>> case nestedToComp nested of EC ((n, ()), hang) k -> (n, fst (hang (Right 7)), k (Right 7, Right 'a'))
-- (5,"7!","a?")
--
-- >>> case compToNested (nestedToComp nested) of EP (EK n, EE f) -> case f 7 of EP (EK s, EE g) -> (n, s, g 'a')
-- (5,"7!","a?")
--
-- Two-step dynamics: @('Exp' Int ∘ 'Exp' Int)@ adds inputs along a path.
--
-- >>> let dyn = EE (\n -> EE (\m -> n + m)) :: Eval ('Exp Int) (Eval ('Exp Int) Int)
-- >>> case nestedToComp dyn of EC ((), hang) k -> k (10, 20)
-- 30
--
-- >>> case compToNested (nestedToComp dyn) of EE f -> case f 10 of EE g -> g 20
-- 30

-- ** Tensor wiring

--
-- 'tensorEval' pairs factors; both pin maps must contribute (not just the
-- left factor).
--
-- >>> let va = EE (\x -> x ++ "x") :: Eval ('Exp String) String
-- >>> let vb = EE (\n -> n * 10) :: Eval ('Exp Int) Int
-- >>> case tensorEval va vb of ET ((), ()) f -> (f ("hi", 3), f ("", 0))
-- (("hix",30),("x",0))
--
-- 'parWiring' places two monomial systems side by side; 'parT' maps the
-- wired interface (wire-then-map).
--
-- >>> let sysN = (\s -> EP (EK (s + 1), EE (\dn -> s + dn))) :: System Int (Mono Int Int)
-- >>> let sysB = (\b -> EP (EK b, EE (\db -> b && db))) :: System Bool (Mono Bool Bool)
-- >>> case parWiring sysN sysB (3, True) of ET ((n, ()), (c, ())) f -> (n, c, f (Right 2, Right False))
-- (4,True,(5,False))
--
-- >>> let m1 = lens show (\n dn -> n + dn) :: Morphism (Mono Int Int) (Mono String Int)
-- >>> let m2 = lens (\b -> if b then 1 else 0 :: Int) (\b db -> b && db) :: Morphism (Mono Bool Bool) (Mono Int Bool)
-- >>> let wired = parWiring sysN sysB (5, True)
-- >>> case parT m1 m2 wired of ET ((_, ()), (_, ())) f -> f (Right 3, Right True)
-- (14,True)

-- | The monomial interface: @a@ positions, @a'@ directions.
type Mono a a' = 'Prod ('Const a) ('Exp a')

-- | The general point-dependent lens.
--
-- Forward pass @get :: a -> b@; backward pass @put :: a -> db -> da@
-- depends on the current position.
--
-- >>> let l = lens show (\n d -> n + d) :: Morphism (Mono Int Int) (Mono String Int)
-- >>> let (v, put) = applyLens l 40 in (v, put 2)
-- ("40",42)
lens :: (a -> b) -> (a -> db -> da) -> Morphism (Mono a da) (Mono b db)
lens f g = Depend (\a -> Pair (Konst (f a)) (ExpMap (g a)))

-- | The position-independent dagger case.
--
-- Expressible without 'Konst' or 'Depend'.
--
-- >>> let d = dagger (+1) (subtract 1) :: Morphism (Mono Int Int) (Mono Int Int)
-- >>> let (v, put) = applyLens d 5 in (v, put 6)
-- (6,5)
dagger :: (a -> b) -> (db -> da) -> Morphism (Mono a da) (Mono b db)
dagger f g = Pair (Compose (ConstMap f) Fst) (Compose (ExpMap g) Snd)

-- | Apply a monomial morphism as a lens: @(get, put)@.
applyLens :: Morphism (Mono a da) (Mono b db) -> a -> (b, db -> da)
applyLens m a = case runMorphism m (EP (EK a, EE id)) of
  EP (EK b, EE g) -> (b, g)

-- | A dynamical system with interface @p@ and state type @s@.
--
-- For the polynomial @Prod (Const o) (Exp i)@ this is the usual Moore
-- machine: expose an output @o@ and accept an input @i@ to determine the
-- next state.
type System s (p :: Poly) = s -> Eval p s

-- | Run one step: observe the current @p@-output from state @s@.
step :: System s p -> s -> Eval p s
step = id
