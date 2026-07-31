{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

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
--
-- The DSL is a /deep embedding/: every value remembers how it was built.
-- That lets us interpret a diagram either as an executable 'IntMorph' (via
-- 'runDiagram') or as an untyped drawing skeleton (via 'skeleton') for a
-- renderer such as @chart-svg@.
module Circuit.Poly.StringDiagram
  ( -- * String-diagram vocabulary
    Wire,
    Diagram,
    wire,
    box,
    boxLabelled,
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

    -- * Drawing skeleton
    SDiagram (..),
    skeleton,
  )
where

import Circuit.Category qualified as Cat
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Poly (Mono, Morphism, applyLens)
import Circuit.Poly.Int (IN, IntMorph (..))
import Circuit.Poly.Int qualified as Int
import Circuit.Tensor qualified as M
import Prelude hiding (id, (.))

-- | A wire is a forward type paired with a backward type.
type Wire a da = IN a da

-- | Untyped drawing syntax for a string diagram.
--
-- This is what a renderer consumes.  It discards the Haskell types but
-- keeps the layout structure: boxes, wires, bends, swaps, composition and
-- tensor.
data SDiagram
  = -- | Straight identity wire.
    SWire
  | -- | Box with a label.
    SBox String
  | -- | Prism box.
    SPrismBox
  | -- | Two diagrams side by side (tensor product).
    SBeside SDiagram SDiagram
  | -- | Two diagrams chained (composition).
    SThenD SDiagram SDiagram
  | -- | Cup (counit): bends two wires back to the unit.
    SBend
  | -- | Cap (unit): introduces two wires from the unit.
    SBend'
  | -- | Dual (rotate 180°).
    STurn SDiagram
  | -- | Left unitor @I \u2297 A -> A@.
    SUnitL
  | -- | Inverse left unitor @A -> I \u2297 A@.
    SUnitL'
  | -- | Right unitor @A \u2297 I -> A@.
    SUnitR
  | -- | Inverse right unitor @A -> A \u2297 I@.
    SUnitR'
  | -- | Associator @A \u2297 (B \u2297 C) -> (A \u2297 B) \u2297 C@.
    SAssoc
  | -- | Inverse associator @(A \u2297 B) \u2297 C -> A \u2297 (B \u2297 C)@.
    SAssoc'
  | -- | Symmetric braiding @A \u2297 B -> B \u2297 A@.
    SSwap
  deriving (Eq, Show)

-- | Internal deep embedding of a typed string diagram.
--
-- The constructors mirror the public smart constructors exactly.
data Diagram_ a da b db where
  Wire_ :: Diagram_ a da a da
  Box_ :: String -> Morphism (Mono da a) (Mono db b) -> Diagram_ a da b db
  PrismBox_ ::
    (s -> Either a s) ->
    (a -> s) ->
    Diagram_ s s (Either a s) (Either a s)
  Beside_ ::
    Diagram_ ap am bp bm ->
    Diagram_ cp cm dp dm ->
    Diagram_ (ap, cp) (am, cm) (bp, dp) (bm, dm)
  ThenD_ ::
    Diagram_ ap am bp bm ->
    Diagram_ bp bm cp cm ->
    Diagram_ ap am cp cm
  Bend_ :: Diagram_ (da, a) (a, da) () ()
  Bend'_ :: Diagram_ () () (a, da) (da, a)
  Turn_ :: Diagram_ a da b db -> Diagram_ db b da a
  UnitL_ :: Diagram_ ((), a) ((), da) a da
  UnitL'_ :: Diagram_ a da ((), a) ((), da)
  UnitR_ :: Diagram_ (a, ()) (da, ()) a da
  UnitR'_ :: Diagram_ a da (a, ()) (da, ())
  Assoc_ ::
    Diagram_ (a, (b, c)) (da, (db, dc)) ((a, b), c) ((da, db), dc)
  Assoc'_ ::
    Diagram_ ((a, b), c) ((da, db), dc) (a, (b, c)) (da, (db, dc))
  Swap_ ::
    Diagram_ (a, b) (da, db) (b, a) (db, da)

-- | A string diagram from one bundle of wires to another.
--
-- The base category is 'Loop (,) (->)' so that sequential composition can
-- tie feedback knots.
newtype Diagram a da b db = Diagram (Diagram_ a da b db)

-- | Forget the types and extract the drawing skeleton.
skeleton :: Diagram a da b db -> SDiagram
skeleton (Diagram d) = go d
  where
    go :: Diagram_ a' da' b' db' -> SDiagram
    go Wire_ = SWire
    go (Box_ lbl _) = SBox lbl
    go (PrismBox_ _ _) = SPrismBox
    go (Beside_ f g) = SBeside (go f) (go g)
    go (ThenD_ f g) = SThenD (go f) (go g)
    go Bend_ = SBend
    go Bend'_ = SBend'
    go (Turn_ f) = STurn (go f)
    go UnitL_ = SUnitL
    go UnitL'_ = SUnitL'
    go UnitR_ = SUnitR
    go UnitR'_ = SUnitR'
    go Assoc_ = SAssoc
    go Assoc'_ = SAssoc'
    go Swap_ = SSwap

-- | Convert a deep-embedding diagram back to the executable Int corridor.
toIntMorph :: Diagram a da b db -> IntMorph (,) (Loop (,) (->)) a da b db
toIntMorph (Diagram d) = case d of
  Wire_ -> IntMorph (Lift M.swap)
  Box_ _ m -> IntMorph (Lift (\(a, db) -> let (b, put) = applyLens m a in (put db, b)))
  PrismBox_ match build ->
    IntMorph
      ( Lift
          ( \(s, e) -> case e of
              Left a -> (build a, match s)
              Right s' -> (s', match s)
          )
      )
  Beside_ f g -> besideInt (toIntMorph (Diagram f)) (toIntMorph (Diagram g))
  ThenD_ f g -> Int.comp (toIntMorph (Diagram g)) (toIntMorph (Diagram f))
  Bend_ -> IntMorph (Lift (\((da, a), ()) -> ((a, da), ())))
  Bend'_ -> IntMorph (Lift (\((), (da, a)) -> ((), (a, da))))
  Turn_ f -> turnInt (toIntMorph (Diagram f))
  UnitL_ -> IntMorph (Lift (runIntMorph Int.unitL))
  UnitL'_ -> IntMorph (Lift (runIntMorph Int.unitL'))
  UnitR_ -> IntMorph (Lift (runIntMorph Int.unitR))
  UnitR'_ -> IntMorph (Lift (runIntMorph Int.unitR'))
  Assoc_ -> IntMorph (Lift (runIntMorph Int.tensorAssoc))
  Assoc'_ -> IntMorph (Lift (runIntMorph Int.tensorAssoc'))
  Swap_ -> IntMorph (Lift (runIntMorph Int.braid))

-- | The identity diagram: a straight wire.
--
-- In the Int construction identity is the symmetry that swaps the forward
-- and backward factors.
wire :: Diagram a da a da
wire = Diagram Wire_

-- | A box built from a causal dependent lens.
box :: Morphism (Mono da a) (Mono db b) -> Diagram a da b db
box = boxLabelled "box"

-- | A labelled box built from a causal dependent lens.
boxLabelled :: String -> Morphism (Mono da a) (Mono db b) -> Diagram a da b db
boxLabelled lbl m = Diagram (Box_ lbl m)

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
prismBox match build = Diagram (PrismBox_ match build)

-- | Place two diagrams side by side (tensor product).
beside ::
  Diagram ap am bp bm ->
  Diagram cp cm dp dm ->
  Diagram (ap, cp) (am, cm) (bp, dp) (bm, dm)
beside (Diagram f) (Diagram g) = Diagram (Beside_ f g)

-- | Chain two diagrams sequentially.
--
-- @f ">>' g@ means "first @f@, then @g@" — i.e. categorical composition
-- @g . f@.
thenD ::
  Diagram ap am bp bm ->
  Diagram bp bm cp cm ->
  Diagram ap am cp cm
thenD (Diagram f) (Diagram g) = Diagram (ThenD_ f g)

-- | Introduce two wires from nothing to form a cap (unit).
--
-- At object @IN a da@ the cap produces @IN (a, da) (da, a)@.
bend' :: Diagram () () (a, da) (da, a)
bend' = Diagram Bend'_

-- | Bend two wires back to form a cup (counit).
--
-- At object @IN a da@ the cup consumes the dual pair @IN (da, a) (a, da)@.
bend :: Diagram (da, a) (a, da) () ()
bend = Diagram Bend_

-- | Turn a diagram around: dual in the compact closed sense.
turn :: Diagram a da b db -> Diagram db b da a
turn (Diagram f) = Diagram (Turn_ f)

-- | Left unitor: @I \u2297 A -> A@.
unitL :: Diagram ((), a) ((), da) a da
unitL = Diagram UnitL_

-- | Inverse left unitor: @A -> I \u2297 A@.
unitL' :: Diagram a da ((), a) ((), da)
unitL' = Diagram UnitL'_

-- | Right unitor: @A \u2297 I -> A@.
unitR :: Diagram (a, ()) (da, ()) a da
unitR = Diagram UnitR_

-- | Inverse right unitor: @A -> A \u2297 I@.
unitR' :: Diagram a da (a, ()) (da, ())
unitR' = Diagram UnitR'_

-- | Associator: @A \u2297 (B \u2297 C) -> (A \u2297 B) \u2297 C@.
assoc ::
  Diagram (a, (b, c)) (da, (db, dc)) ((a, b), c) ((da, db), dc)
assoc = Diagram Assoc_

-- | Inverse associator: @(A \u2297 B) \u2297 C -> A \u2297 (B \u2297 C)@.
assoc' ::
  Diagram ((a, b), c) ((da, db), dc) (a, (b, c)) (da, (db, dc))
assoc' = Diagram Assoc'_

-- | Symmetric braiding: @A \u2297 B -> B \u2297 A@.
swap ::
  Diagram (a, b) (da, db) (b, a) (db, da)
swap = Diagram Swap_

-- | Run a closed string diagram on a concrete input.
--
-- The input is a forward value together with a backward cotangent; the
-- output is the backward cotangent on the input side together with the
-- forward value on the output side.
runDiagram :: Diagram a da b db -> (a, db) -> (da, b)
runDiagram d = run (runIntMorph (toIntMorph d))

-- Internal helpers (reused from the previous shallow-embedding definitions).

besideInt ::
  IntMorph (,) (Loop (,) (->)) ap am bp bm ->
  IntMorph (,) (Loop (,) (->)) cp cm dp dm ->
  IntMorph (,) (Loop (,) (->)) (ap, cp) (am, cm) (bp, dp) (bm, dm)
besideInt (IntMorph f) (IntMorph g) = IntMorph (Lift permOut Cat.. (f `M.par` g) Cat.. Lift permIn)
  where
    permIn :: ((ap, cp), (bm, dm)) -> ((ap, bm), (cp, dm))
    permIn ((ap, cp), (bm, dm)) = ((ap, bm), (cp, dm))

    permOut :: ((am, bp), (cm, dp)) -> ((am, cm), (bp, dp))
    permOut ((am, bp), (cm, dp)) = ((am, cm), (bp, dp))

turnInt ::
  IntMorph (,) (Loop (,) (->)) a da b db ->
  IntMorph (,) (Loop (,) (->)) db b da a
turnInt (IntMorph f) = IntMorph (Lift M.swap Cat.. f Cat.. Lift M.swap)
