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
-- names and runs the diagrams over 'Trace (,) (->)' so that feedback loops
-- are tied into yanked traces.
--
-- The DSL is a /deep embedding/: every value remembers how it was built.
-- That lets us interpret a diagram either as an executable 'IntMorph' (via
-- 'runDiagram') or as an untyped drawing skeleton (via 'skeleton') for a
-- renderer such as @chart-svg@.
--
-- The skeleton also carries hypergraph syntax: multi-port boxes and
-- spiders ('SSpider', with 'sCopy' \/ 'sMerge' \/ 'sDelete' \/ 'sCreate'
-- as the usual generators).  Spiders are drawing-level syntax only —
-- there are deliberately no spider constructors in the typed 'Diagram'
-- GADT, so 'skeleton' never produces one.  Structural comparison of the
-- hyper fragment lives in "Circuit.Diagram.Hyper".
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
    traceD,

    -- * Running a diagram
    runDiagram,

    -- * Drawing skeleton (re-exported from "Circuit.Diagram")
    SDiagram (..),
    skeleton,
    sCopy,
    sMerge,
    sDelete,
    sCreate,
  )
where

import Circuit.Category qualified as Cat
import Circuit.Channel (Traced (..))
import Circuit.Diagram (SDiagram (..), sCopy, sCreate, sDelete, sMerge)
import Circuit.Syntax (eval)
import Circuit.Trace (Trace, base)
import Circuit.Poly (Mono, Morphism, applyLens)
import Circuit.Poly.Int (IN, IntMorph (..))
import Circuit.Poly.Int qualified as Int
import Circuit.Tensor qualified as M
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude

-- | A wire is a forward type paired with a backward type.
type Wire a da = IN a da

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
  Trace_ ::
    Diagram_ (s, a) (s, da) (s, b) (s, db) ->
    Diagram_ a da b db

-- | A string diagram from one bundle of wires to another.
--
-- The base category is 'Trace (,) (->)' so that sequential composition can
-- tie feedback knots.
newtype Diagram a da b db = Diagram (Diagram_ a da b db)

-- | Forget the types and extract the drawing skeleton.
skeleton :: Diagram a da b db -> SDiagram
skeleton (Diagram d) = go d
  where
    go :: Diagram_ a' da' b' db' -> SDiagram
    go Wire_ = SWire
    go (Box_ lbl _) = SBox lbl 1 1
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
    go (Trace_ f) = STrace (go f)

-- | Convert a deep-embedding diagram back to the executable Int corridor.
toIntMorph :: Diagram a da b db -> IntMorph (,) (Trace (,) (->)) a da b db
toIntMorph (Diagram d) = case d of
  Wire_ -> IntMorph (base M.swap)
  Box_ _ m -> IntMorph (base (\(a, db) -> let (b, put) = applyLens m a in (put db, b)))
  PrismBox_ match build ->
    IntMorph
      ( base
          ( \(s, e) -> case e of
              Left a -> (build a, match s)
              Right s' -> (s', match s)
          )
      )
  Beside_ f g -> Int.par (toIntMorph (Diagram f)) (toIntMorph (Diagram g))
  ThenD_ f g -> Int.comp (toIntMorph (Diagram g)) (toIntMorph (Diagram f))
  Bend_ -> IntMorph (base (\((da, a), ()) -> ((a, da), ())))
  Bend'_ -> IntMorph (base (\((), (da, a)) -> ((), (a, da))))
  Turn_ f -> turnInt (toIntMorph (Diagram f))
  UnitL_ -> IntMorph (base (runIntMorph Int.unitL))
  UnitL'_ -> IntMorph (base (runIntMorph Int.unitL'))
  UnitR_ -> IntMorph (base (runIntMorph Int.unitR))
  UnitR'_ -> IntMorph (base (runIntMorph Int.unitR'))
  Assoc_ -> IntMorph (base (runIntMorph Int.tensorAssoc))
  Assoc'_ -> IntMorph (base (runIntMorph Int.tensorAssoc'))
  Swap_ -> IntMorph (base (runIntMorph Int.braid))
  Trace_ f -> traceIntMorph (toIntMorph (Diagram f))
  where
    traceIntMorph ::
      IntMorph (,) (Trace (,) (->)) (s, a) (s, da) (s, b) (s, db) ->
      IntMorph (,) (Trace (,) (->)) a da b db
    traceIntMorph (IntMorph body) =
      IntMorph
        ( trace
            ( base (\((s1, s2), (da, b)) -> ((s1, da), (s2, b)))
                Cat.. body
                Cat.. base (\((s1, s2), (a, db)) -> ((s1, a), (s2, db)))
            )
        )

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

-- | Hide a feedback wire: trace over the state @s@.
--
-- The body has one extra input/output pair @s@ that is fed back to itself.
traceD ::
  Diagram (s, a) (s, da) (s, b) (s, db) ->
  Diagram a da b db
traceD (Diagram f) = Diagram (Trace_ f)

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

-- $snake-equations
--
-- The cap/cup pair on a self-dual finite object satisfies the snake
-- equations up to diagram deformation. For @IN Bool Bool@ both snakes
-- round-trip to the identity wire:
--
-- >>> :{
-- let snakeR :: Diagram Bool Bool Bool Bool
--     snakeR = unitR' `thenD` (wire `beside` bend') `thenD` assoc `thenD` (bend `beside` wire) `thenD` unitL
--     snakeL :: Diagram Bool Bool Bool Bool
--     snakeL = unitL' `thenD` (bend' `beside` wire) `thenD` assoc' `thenD` (wire `beside` bend) `thenD` unitR
--     inputs = [(a, b) | a <- [False, True], b <- [False, True]]
-- in ( and [runDiagram snakeR i == runDiagram wire i | i <- inputs]
--    , and [runDiagram snakeL i == runDiagram wire i | i <- inputs]
--    )
-- :}
-- (True,True)

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
runDiagram d = eval (runIntMorph (toIntMorph d))

-- Internal helpers (reused from the previous shallow-embedding definitions).

turnInt ::
  IntMorph (,) (Trace (,) (->)) a da b db ->
  IntMorph (,) (Trace (,) (->)) db b da a
turnInt (IntMorph f) = IntMorph (base M.swap Cat.. f Cat.. base M.swap)
