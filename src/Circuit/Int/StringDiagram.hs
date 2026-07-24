{-# LANGUAGE DataKinds #-}

-- | A small string-diagram surface syntax over the Int construction.
--
-- The Int corridor turns a traced monoidal base category into a compact
-- closed category.  For the causal fragment of 'Circuit.Poly' — dependent
-- lenses between monomial interfaces — the resulting diagrams are exactly
-- the usual boxes-and-wires pictures: a wire is a polarity pair, a box is a
-- causal lens, placing diagrams beside each other is tensor, chaining them
-- is composition, and bending a wire back uses the compact-closed cap/cup.
--
-- This module aliases the underlying Int machinery with string-diagram
-- names and runs the diagrams over 'Loop (,) (->)' so that feedback loops
-- are tied into one-'Knot' normal form.
module Circuit.Int.StringDiagram
  ( -- * String-diagram vocabulary
    Wire,
    Diagram,
    wire,
    box,
    beside,
    thenD,
    bend,
    bend',
    turn,
    unitL,
    unitL',
    unitR,
    unitR',
    assoc,
    assoc',
    swap,
    prismBox,

    -- * Running a diagram
    runDiagram,
  )
where

import Circuit.Category qualified as Cat
import Circuit.Int (IN, IntMorph (..))
import Circuit.Int qualified as Int
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Poly (Mono, Morphism, applyLens)
import Circuit.Tensor qualified as M
import Prelude hiding (id, (.))

-- | A wire is a forward type paired with a backward type.
type Wire a da = IN a da

-- | A string diagram from one bundle of wires to another.
--
-- The base category is 'Loop (,) (->)' so that sequential composition can
-- tie feedback knots.
type Diagram a da b db = IntMorph (,) (Loop (,) (->)) a da b db

-- | The identity diagram: a straight wire.
--
-- In the Int construction identity is the symmetry that swaps the forward
-- and backward factors.
wire :: Diagram a da a da
wire = IntMorph (Lift M.swap)

-- | A box built from a causal dependent lens.
box :: Morphism (Mono a da) (Mono b db) -> Diagram a da b db
box m = IntMorph (Lift (\(a, db) -> let (b, put) = applyLens m a in (put db, b)))

-- | A prism box: partial access to a sum-shaped position.
--
-- Forward pass @match :: s -> Either a s@; backward pass uses @build :: a -> s@
-- on the matched branch and the identity on the unmatched branch.  Directions
-- are identified with positions, the natural reading for set-valued
-- polynomials.
prismBox ::
  (s -> Either a s) ->
  (a -> s) ->
  Diagram s s (Either a s) (Either a s)
prismBox match build = IntMorph (Lift (\(s, e) ->
  case e of
    Left a -> (build a, match s)
    Right s' -> (s', match s)))

-- | Place two diagrams side by side (tensor product).
beside ::
  Diagram ap am bp bm ->
  Diagram cp cm dp dm ->
  Diagram (ap, cp) (am, cm) (bp, dp) (bm, dm)
beside (IntMorph f) (IntMorph g) = IntMorph (Lift permOut Cat.. (f `M.par` g) Cat.. Lift permIn)
  where
    permIn :: ((ap, cp), (bm, dm)) -> ((ap, bm), (cp, dm))
    permIn ((ap, cp), (bm, dm)) = ((ap, bm), (cp, dm))

    permOut :: ((am, bp), (cm, dp)) -> ((am, cm), (bp, dp))
    permOut ((am, bp), (cm, dp)) = ((am, cm), (bp, dp))

-- | Chain two diagrams sequentially.
--
-- @f ">>" g@ means "first @f@, then @g@" — i.e. categorical composition
-- @g . f@.
thenD ::
  Diagram ap am bp bm ->
  Diagram bp bm cp cm ->
  Diagram ap am cp cm
thenD f g = Int.comp g f

-- | Introduce two wires from nothing to form a cap (unit).
--
-- At object @IN a da@ the cap produces @IN (a, da) (da, a)@.
bend' :: Diagram () () (a, da) (da, a)
bend' = IntMorph (Lift (\((), (da, a)) -> ((), (a, da))))

-- | Bend two wires back to form a cup (counit).
--
-- At object @IN a da@ the cup consumes the dual pair @IN (da, a) (a, da)@.
bend :: Diagram (da, a) (a, da) () ()
bend = IntMorph (Lift (\((da, a), ()) -> ((a, da), ())))

-- | Turn a diagram around: dual in the compact closed sense.
turn :: Diagram a da b db -> Diagram db b da a
turn (IntMorph f) = IntMorph (Lift M.swap Cat.. f Cat.. Lift M.swap)

-- | Left unitor: @I \u2297 A -> A@.
unitL :: Diagram ((), a) ((), da) a da
unitL = IntMorph (Lift (runIntMorph Int.unitL))

-- | Inverse left unitor: @A -> I \u2297 A@.
unitL' :: Diagram a da ((), a) ((), da)
unitL' = IntMorph (Lift (runIntMorph Int.unitL'))

-- | Right unitor: @A \u2297 I -> A@.
unitR :: Diagram (a, ()) (da, ()) a da
unitR = IntMorph (Lift (runIntMorph Int.unitR))

-- | Inverse right unitor: @A -> A \u2297 I@.
unitR' :: Diagram a da (a, ()) (da, ())
unitR' = IntMorph (Lift (runIntMorph Int.unitR'))

-- | Associator: @A \u2297 (B \u2297 C) -> (A \u2297 B) \u2297 C@.
assoc ::
  Diagram (a, (b, c)) (da, (db, dc)) ((a, b), c) ((da, db), dc)
assoc = IntMorph (Lift (runIntMorph Int.tensorAssoc))

-- | Inverse associator: @(A \u2297 B) \u2297 C -> A \u2297 (B \u2297 C)@.
assoc' ::
  Diagram ((a, b), c) ((da, db), dc) (a, (b, c)) (da, (db, dc))
assoc' = IntMorph (Lift (runIntMorph Int.tensorAssoc'))

-- | Symmetric braiding: @A \u2297 B -> B \u2297 A@.
swap ::
  Diagram (a, b) (da, db) (b, a) (db, da)
swap = IntMorph (Lift (runIntMorph Int.braid))

-- | Run a closed string diagram on a concrete input.
--
-- The input is a forward value together with a backward cotangent; the
-- output is the backward cotangent on the input side together with the
-- forward value on the output side.
runDiagram :: Diagram a da b db -> (a, db) -> (da, b)
runDiagram d = run (runIntMorph d)
