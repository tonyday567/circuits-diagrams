{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Int construction: free compact closure over a traced monoidal
-- category.
--
-- For a traced monoidal category @(t, arr)@, objects of @Int (t, arr)@ are
-- polarity pairs @(a\u207a, a\u207b)@, wrapped in the phantom type 'IN'. A
-- morphism from @(ap, am)@ to @(bp, bm)@ is a base morphism
-- @arr (t ap bm) (t am bp)@.
--
-- Identity is the symmetry on the two factors. Composition tensors the two
-- base morphisms, reassociates so the middle pair can be eliminated, and
-- closes it with the base category's 'trace'. Over @Trace t arr@ this means
-- every composite inherits the one-'Yank' normal form.
--
-- This module uses only the 'Trace'/'Channel' surface and introduces no
-- new dependencies.
module Circuit.Poly.Int
  ( -- * Int objects and morphisms
    IN,
    IntMorph (..),

    -- * Compact-closed structure
    id,
    comp,
    dual,

    -- * Tensor product of Int morphisms
    intTensor,

    -- * Unit and coherence (yanking witnesses)
    cap,
    cup,
    unitL,
    unitL',
    unitR,
    unitR',
    tensorAssoc,
    tensorAssoc',
    assocInv,
    intBraid,

    -- * Bridge from Poly monomial lenses
    causal,
  )
where

import Circuit.Category ((.))
import Circuit.Category qualified as Cat (Category (..))
import Circuit.Channel (Channel (..), Traced (..))
import Circuit.Poly (Mono, Morphism (Compose), applyLens, lens)
import Circuit.Syntax (Syntax (..), eval, (:+:) (..))
import Circuit.Tensor qualified as M (Action (..), Tensor (..))
import Circuit.Trace (SigYank (..), Trace, base, yank)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Circuit.Category ((.))
-- >>> import Circuit.Category qualified as Cat
-- >>> import Circuit.Trace (Trace, SigYank (..), base, yank)
-- >>> import Circuit.Syntax (Syntax (..), (:+:) (..), eval)
-- >>> import Circuit.Channel (Traced (..), Channel (..), trace)
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Circuit.Poly (dagger, lens, applyLens, Morphism (..), Mono)
-- >>> import Data.Bifunctor (Bifunctor (..))
-- >>> :set -XGADTs -XStandaloneDeriving -XFlexibleInstances -XFlexibleContexts -XScopedTypeVariables -XTypeApplications
-- >>> isYank :: Trace (,) (->) a b -> Bool; isYank x = case x of { Op (R (Yank _)) -> True; _ -> False }
-- >>> class Eq a => Finite a where universe :: [a]
-- >>> instance Finite () where universe = [()]
-- >>> instance Finite Bool where universe = [False, True]
-- >>> instance (Finite a, Finite b) => Finite (Either a b) where universe = map Left universe ++ map Right universe
-- >>> :{
-- data Mat i j where
--   Id :: Mat i i
--   MatR :: (Finite i, Finite j) => [(i, j)] -> Mat i j
-- :}
--
-- >>> :{
-- mat :: (Finite i, Finite j) => (i -> j -> Bool) -> Mat i j
-- mat f = MatR [(i, j) | i <- universe, j <- universe, f i j]
-- :}
--
-- >>> :{
-- runMat :: (Eq i, Eq j) => Mat i j -> i -> j -> Bool
-- runMat Id i j = i == j
-- runMat (MatR pairs) i j = (i, j) `elem` pairs
-- :}
--
-- >>> :{
-- instance Cat.Category Mat where
--   id = Id
--   Id . f = f
--   f . Id = f
--   MatR g . MatR f = MatR [(i, k) | (i, j) <- f, (j', k) <- g, j == j']
-- :}
--
-- >>> :{
-- matPar :: (Finite a, Finite b, Finite c, Finite d) => Mat a b -> Mat c d -> Mat (Either a c) (Either b d)
-- matPar f g = mat $ \case
--   Left a -> \case Left b -> runMat f a b; _ -> False
--   Right c -> \case Right d -> runMat g c d; _ -> False
-- :}
--
-- >>> :{
-- matSwap :: (Finite a, Finite b) => Mat (Either a b) (Either b a)
-- matSwap = mat $ \case
--   Left a -> \case Right a' -> a == a'; _ -> False
--   Right b -> \case Left b' -> b == b'; _ -> False
-- :}
--
-- >>> :{
-- matAssoc :: (Finite a, Finite b, Finite c) => Mat (Either (Either a b) c) (Either a (Either b c))
-- matAssoc = mat $ \case
--   Left (Left a) -> \case Left a' -> a == a'; _ -> False
--   Left (Right b) -> \case Right (Left b') -> b == b'; _ -> False
--   Right c -> \case Right (Right c') -> c == c'; _ -> False
-- :}
--
-- >>> :{
-- matAssoc' :: (Finite a, Finite b, Finite c) => Mat (Either a (Either b c)) (Either (Either a b) c)
-- matAssoc' = mat $ \case
--   Left a -> \case Left (Left a') -> a == a'; _ -> False
--   Right (Left b) -> \case Left (Right b') -> b == b'; _ -> False
--   Right (Right c) -> \case Right c' -> c == c'; _ -> False
-- :}
--
-- >>> :{
-- matBraid :: (Finite a, Finite b, Finite c) => Mat (Either a (Either b c)) (Either b (Either a c))
-- matBraid = mat $ \case
--   Left a -> \case Right (Left a') -> a == a'; _ -> False
--   Right (Left b) -> \case Left b' -> b == b'; _ -> False
--   Right (Right c) -> \case Right (Right c') -> c == c'; _ -> False
-- :}
--
-- >>> :{
-- matTrace :: (Finite a, Finite b, Finite c) => Mat (Either a b) (Either a c) -> Mat b c
-- matTrace f = mat $ \b c ->
--   runMat f (Right b) (Right c) ||
--   or [runMat f (Right b) (Left a) && runMat f (Left a') (Right c)
--       | a <- universe, a' <- universe]
-- :}
--
-- >>> :{
-- compMatEither ::
--   forall ap am bp bm cp cm.
--   (Finite ap, Finite am, Finite bp, Finite bm, Finite cp, Finite cm) =>
--   IntMorph Either Mat bp bm cp cm ->
--   IntMorph Either Mat ap am bp bm ->
--   IntMorph Either Mat ap am cp cm
-- compMatEither (IntMorph g) (IntMorph f) = IntMorph (matTrace (middleOut . matPar g f . middleIn))
--   where
--     id_ap = Cat.id :: Mat ap ap
--     id_am = Cat.id :: Mat am am
--     id_bm = Cat.id :: Mat bm bm
--     middleIn =
--       matSwap @(Either ap bm) @(Either bp cm)
--         . matAssoc' @ap @bm @(Either bp cm)
--         . (id_ap `matPar` matAssoc @bm @bp @cm)
--         . (id_ap `matPar` matSwap @cm @(Either bm bp))
--         . matAssoc @ap @cm @(Either bm bp)
--         . matSwap @(Either bm bp) @(Either ap cm)
--     middleOut =
--       matSwap @(Either am cp) @(Either bm bp)
--         . matBraid @bm @(Either am cp) @bp
--         . (id_bm `matPar` matAssoc' @am @cp @bp)
--         . (id_bm `matPar` (id_am `matPar` matSwap @bp @cp))
--         . (id_bm `matPar` matAssoc @am @bp @cp)
--         . (id_bm `matPar` matSwap @cp @(Either am bp))
--         . matAssoc @bm @cp @(Either am bp)
-- :}

-- | Phantom polarity pair.  @IN ap am@ is the Int object with forward
-- face @ap@ and backward face @am@.
data IN (ap :: Type) (am :: Type)

-- | A morphism in the Int construction from @(ap, am)@ to @(bp, bm)@ over
-- a traced monoidal base category.
--
-- The underlying arrow runs from the forward input plus the backward output
-- (@t ap bm@) to the backward input plus the forward output (@t am bp@).
newtype IntMorph (t :: Type -> Type -> Type) arr (ap :: Type) (am :: Type) (bp :: Type) (bm :: Type) = IntMorph
  { -- | Extract the underlying base morphism.
    runIntMorph :: arr (t ap bm) (t am bp)
  }

-- | Identity in @Int@ is the symmetry that swaps the two factors.
--
-- >>> let i = id :: IntMorph (,) (->) Int Bool Int Bool
-- >>> runIntMorph i (1, False)
-- (False,1)
id :: (M.Action t arr) => IntMorph t arr ap am ap am
id = IntMorph M.braid

-- | Dual of an Int morphism: swap the polarities of domain and codomain.
--
-- The underlying arrow is pre- and post-composed with the symmetry so that
-- the types line up: @arr (t bm ap) (t bp am)@.
--
-- >>> let f = IntMorph (\(a, d) -> (a * 2, d + 1)) :: IntMorph (,) (->) Int Int Int Int
-- >>> runIntMorph (dual f) (5, 1)
-- (6,2)
dual :: (M.Action t arr) => IntMorph t arr ap am bp bm -> IntMorph t arr bm bp am ap
dual (IntMorph f) = IntMorph (M.braid . f . M.braid)

-- | Composition in the Int construction.
--
-- Tensor the two base morphisms, reassociate the four factors so the middle
-- pair @(bm, bp)@ sits on the feedback wire, and close it with 'trace'. The
-- result is again a single base arrow @arr (t ap cm) (t am cp)@.
--
-- Nontrivial composition over @Trace (,) (->)@.  Both morphisms transform
-- both legs; the middle trace closes the feedback loop.  The chosen bodies
-- are lazy in the feedback component so the lazy @(,)@ knot stays productive.
-- Hand-computed: input @(4, 1)@ gives output @(5, 2)@.
--
-- >>> let f = IntMorph (base (\(a, _) -> (a + 1, a))) :: IntMorph (,) (Trace (,) (->)) Int Int Int Int
-- >>> let g = IntMorph (base (\(_, c) -> (c, c + 1))) :: IntMorph (,) (Trace (,) (->)) Int Int Int Int
-- >>> eval (runIntMorph (g `comp` f)) (4, 1)
-- (5,2)
--
-- The composite over @Trace@ inherits the one-'Yank' normal form: the inner
-- plumbing is absorbed into a single 'yank' over one base arrow.
--
-- >>> if isYank (runIntMorph (g `comp` f)) then "one-Yank" else "not one-Yank"
-- "one-Yank"
comp ::
  forall t arr ap am bp bm cp cm.
  (M.Action t arr, Traced t arr) =>
  IntMorph t arr bp bm cp cm ->
  IntMorph t arr ap am bp bm ->
  IntMorph t arr ap am cp cm
comp (IntMorph g) (IntMorph f) = IntMorph (trace (middleOut . (g `M.tensor` f) . middleIn))
  where
    id_ap = Cat.id
    id_am = Cat.id
    id_bm = Cat.id

    middleIn = step6 . step5 . step4 . step3 . step2 . step1
      where
        step1 = M.braid @t @arr @(t bm bp) @(t ap cm)
        step2 = assoc @t @arr @ap @cm @(t bm bp)
        step3 = id_ap `M.tensor` M.braid @t @arr @cm @(t bm bp)
        step4 = id_ap `M.tensor` assoc @t @arr @bm @bp @cm
        step5 = assoc' @t @arr @ap @bm @(t bp cm)
        step6 = M.braid @t @arr @(t ap bm) @(t bp cm)

    middleOut = step7 . step6 . step5 . step4 . step3 . step2 . step1
      where
        step1 = assoc @t @arr @bm @cp @(t am bp)
        step2 = id_bm `M.tensor` M.braid @t @arr @cp @(t am bp)
        step3 = id_bm `M.tensor` assoc @t @arr @am @bp @cp
        step4 = id_bm `M.tensor` (id_am `M.tensor` M.braid @t @arr @bp @cp)
        step5 = id_bm `M.tensor` assoc' @t @arr @am @cp @bp
        step6 = slide @t @arr @bm @(t am cp) @bp
        step7 = M.braid @t @arr @(t am cp) @(t bm bp)

-- | Tensor product of two Int morphisms.
--
-- On objects this is componentwise: @(ap, am) \u2297 (cp, cm) = (t ap cp, t am cm)@.
-- On morphisms it threads the two base arrows side-by-side and reassociates
-- the factors into the required @arr (t (t ap cp) (t bm dm)) (t (t am cm) (t bp dp))@ shape.
intTensor ::
  forall t arr ap am bp bm cp cm dp dm.
  (M.Action t arr, Channel t arr) =>
  IntMorph t arr ap am bp bm ->
  IntMorph t arr cp cm dp dm ->
  IntMorph t arr (t ap cp) (t am cm) (t bp dp) (t bm dm)
intTensor (IntMorph f) (IntMorph g) = IntMorph (permOut . (f `M.tensor` g) . permIn)
  where
    id_ap = Cat.id
    id_bm = Cat.id

    permIn = step5 . step4 . step3 . step2 . step1
      where
        step1 = assoc @t @arr @ap @cp @(t bm dm)
        step2 = id_ap `M.tensor` M.braid @t @arr @cp @(t bm dm)
        step3 = id_ap `M.tensor` assoc @t @arr @bm @dm @cp
        step4 = id_ap `M.tensor` (id_bm `M.tensor` M.braid @t @arr @dm @cp)
        step5 = assoc' @t @arr @ap @bm @(t cp dm)

    permOut = step5 . step4 . step3 . step2 . step1
      where
        step1 = assoc @t @arr @am @bp @(t cm dp)
        step2 = id_am `M.tensor` M.braid @t @arr @bp @(t cm dp)
        step3 = id_am `M.tensor` assoc @t @arr @cm @dp @bp
        step4 = id_am `M.tensor` (id_cm `M.tensor` M.braid @t @arr @dp @bp)
        step5 = assoc' @t @arr @am @cm @(t bp dp)

    id_am = Cat.id
    id_cm = Cat.id

-- | Cap (unit introduction) for @Int(->)@ at object @IN a b@.
--
-- The unit object is @IN () ()@; the cap produces the tensor @IN (a, b) (b, a)@.
cap :: IntMorph (,) (->) () () (a, b) (b, a)
cap = IntMorph $ \ ~((), (b, a)) -> ((), (a, b))

-- | Cup (unit elimination) for @Int(->)@ at object @IN a b@.
cup :: IntMorph (,) (->) (b, a) (a, b) () ()
cup = IntMorph $ \ ~((b, a), ()) -> ((a, b), ())

-- | Left-unitor for @Int(->)@: @I \u2297 A -> A@.
unitL :: IntMorph (,) (->) ((), a) ((), b) a b
unitL = IntMorph $ \ ~(((), a), b) -> (((), b), a)

-- | Inverse left-unitor for @Int(->)@: @A -> I \u2297 A@.
unitR' :: IntMorph (,) (->) a b (a, ()) (b, ())
unitR' = IntMorph $ \ ~(a, (b, ())) -> (b, (a, ()))

-- | Inverse left-unitor for @Int(->)@: @A -> I \u2297 A@.
unitL' :: IntMorph (,) (->) a b ((), a) ((), b)
unitL' = IntMorph $ \ ~(a, ((), b)) -> (b, ((), a))

-- | Right-unitor for @Int(->)@: @A \u2297 I -> A@.
unitR :: IntMorph (,) (->) (a, ()) (b, ()) a b
unitR = IntMorph $ \ ~((a, ()), b) -> ((b, ()), a)

-- | Inverse associator used in the left yanking equation for @IN a b@.
assocInv ::
  IntMorph
    (,)
    (->)
    (a, (b, a))
    (b, (a, b))
    ((a, b), a)
    ((b, a), b)
assocInv = IntMorph $ \ ~((x, (y, x')), ((y', x''), y'')) -> ((y', (x'', y'')), ((x, y), x'))

-- | Associator for @Int(->)@: @A \u2297 (B \u2297 C) -> (A \u2297 B) \u2297 C@.
tensorAssoc ::
  IntMorph
    (,)
    (->)
    (a, (b, c))
    (da, (db, dc))
    ((a, b), c)
    ((da, db), dc)
tensorAssoc = IntMorph $ \ ~((x, (y, z)), ((dx, dy), dz)) -> ((dx, (dy, dz)), ((x, y), z))

-- | Inverse associator for @Int(->)@: @(A \u2297 B) \u2297 C -> A \u2297 (B \u2297 C)@.
tensorAssoc' ::
  IntMorph
    (,)
    (->)
    ((a, b), c)
    ((da, db), dc)
    (a, (b, c))
    (da, (db, dc))
tensorAssoc' = IntMorph $ \ ~(((x, y), z), (dx, (dy, dz))) -> (((dx, dy), dz), (x, (y, z)))

-- | Symmetric braiding for @Int(->)@: @A \u2297 B -> B \u2297 A@.
intBraid ::
  IntMorph
    (,)
    (->)
    (a, b)
    (da, db)
    (b, a)
    (db, da)
intBraid = IntMorph $ \ ~((x, y), (dy, dx)) -> ((dx, dy), (y, x))

-- | Yanking witness.  In the Int construction the identity is the swap on
-- the two factors; tracing that swap over the Either tensor returns the
-- input unchanged.
--
-- >>> let i = id :: IntMorph Either (->) Int Int Int Int
-- >>> trace (runIntMorph i) (42 :: Int)
-- 42

-- | Mat Bool middle trace with coupled blocks.  The feedback channel is
-- @Bool@, the @aa@ block is the swap (so its reflexive-transitive closure is
-- the universal relation on @Bool@), and the off-diagonal @ba@/@ac@ blocks are
-- non-constant.  The helper below repeats the same @parT + slide + trace-middle@
-- wiring as 'comp', but specialised to the @Mat@/Either setup so the
-- doctest can live in the finite-type setting.
--
-- >>> let aa = mat (\a a' -> a /= a') :: Mat Bool Bool
-- >>> let acF = mat (\a c -> a && c) :: Mat Bool Bool
-- >>> let baF = mat (\b a -> b && a) :: Mat Bool Bool
-- >>> let bcF = mat (\_ _ -> False) :: Mat Bool Bool
-- >>> let mF = mat (\x y -> case x of { Left a -> case y of { Left a' -> a /= a'; Right c -> a && c }; Right b -> case y of { Left a' -> b && a'; Right _ -> False } })
-- >>> let f = IntMorph mF :: IntMorph Either Mat Bool Bool Bool Bool
-- >>> let acG = mat (\_ c -> c) :: Mat Bool Bool
-- >>> let baG = mat (\c b -> c || b) :: Mat Bool Bool
-- >>> let mG = mat (\x y -> case x of { Left b -> case y of { Left b' -> b /= b'; Right c -> c }; Right c -> case y of { Left b' -> c || b'; Right _ -> False } })
-- >>> let g = IntMorph mG :: IntMorph Either Mat Bool Bool Bool Bool
-- >>> runMat (runIntMorph (compMatEither g f)) (Right False) (Right False)
-- False
-- >>> runMat (runIntMorph (compMatEither g f)) (Right False) (Right True)
-- True
-- >>> runMat (runIntMorph (compMatEither g f)) (Right True) (Right False)
-- False
-- >>> runMat (runIntMorph (compMatEither g f)) (Right True) (Right True)
-- True

-- | Include a @Poly@ monomial lens as an @Int@ morphism over @(->)@.
--
-- A monomial @'Mono' da a@ is the @Int@ object @'IN' a da@: forward face @a@,
-- backward face @da@. A lens @'Morphism' ('Mono' da a) ('Mono' db b)@ carries a
-- forward pass @a -> b@ and a backward pass @a -> db -> da@; 'causal' packs them
-- into the single joint map @(a, db) -> (da, b)@ that an 'IntMorph' demands.
--
-- This is the /causal fragment/: the forward output @b@ is read from @a@ alone,
-- never from the backward input @db@. The image therefore carries no feedback —
-- composing two 'causal' images under 'comp' leaves the middle 'trace' with
-- nothing to close, so the knot is trivial.
--
-- >>> let l1 = dagger (+10) (*2) :: Morphism (Mono Int Int) (Mono Int Int)
-- >>> runIntMorph (causal l1) (100, 3)
-- (6,110)
--
-- The forward face ignores the backward input — feeding two different backward
-- values leaves the forward output @b@ fixed at @110@:
--
-- >>> [ snd (runIntMorph (causal l1) (100, db)) | db <- [3, 99] ]
-- [110,110]
--
-- Point-dependent lenses cross too: @'lens' 'show' (\\n d -> n + d)@ at @40@ gives
-- forward @"40"@ and backward @40 + 2 = 42@.
--
-- >>> let l2 = lens show (\n d -> n + d) :: Morphism (Mono Int Int) (Mono Int String)
-- >>> runIntMorph (causal l2) (40, 2)
-- (42,"40")
--
-- __Trivial knot under composition.__ Take 'causal' into the 'Trace' base and
-- compose two images with 'comp'. Composition ties a 'Yank' (the middle 'trace'
-- fires) — yet the observed value equals plain lens 'Compose' under the polarity
-- swap, because the causal fragment feeds nothing back through the loop. The knot
-- is tied and does nothing: pullback magnitude of the trace is zero here.
--
-- >>> let cz (m :: Morphism (Mono xd x) (Mono yd y)) = IntMorph (base (\(a, db) -> let (b, put) = applyLens m a in (put db, b))) :: IntMorph (,) (Trace (,) (->)) x xd y yd
-- >>> let f = dagger (+1) (*2) :: Morphism (Mono Int Int) (Mono Int Int)
-- >>> let g = dagger (*10) (+5) :: Morphism (Mono Int Int) (Mono Int Int)
-- >>> let (b, put) = applyLens (Compose g f) 7 in (b, put 100)
-- (80,210)
-- >>> eval (runIntMorph (comp (cz g) (cz f) :: IntMorph (,) (Trace (,) (->)) Int Int Int Int)) (7, 100)
-- (210,80)
-- >>> if isYank (runIntMorph (comp (cz g) (cz f) :: IntMorph (,) (Trace (,) (->)) Int Int Int Int)) then "Yank (tied, trivial)" else "Lift (no knot)"
-- "Yank (tied, trivial)"
causal :: Morphism (Mono da a) (Mono db b) -> IntMorph (,) (->) a da b db
causal m = IntMorph (\(a, db) -> let (b, put) = applyLens m a in (put db, b))

-- $causal-examples
-- See @circuits-repl@ for operational examples of 'causal' wired to a real
-- 'Circuit.Repl' backend.
