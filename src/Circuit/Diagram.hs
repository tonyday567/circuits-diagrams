{-# LANGUAGE GADTs #-}

-- | Generic, untyped string-diagram syntax.
--
-- This is the surface that renderers consume.  It discards the Haskell
-- types but keeps the layout structure: boxes, wires, bends, swaps,
-- composition and tensor.  Constructors live here independently of any
-- particular semantic interpretation (polynomial lenses, matrices, etc.).
module Circuit.Diagram
  ( SDiagram (..),
    sCopy,
    sMerge,
    sDelete,
    sCreate,
  )
where

import Prelude

-- | Untyped drawing syntax for a string diagram.
--
-- This is what a renderer consumes.  It discards the Haskell types but
-- keeps the layout structure: boxes, wires, bends, swaps, composition and
-- tensor.
data SDiagram
  = -- | Straight identity wire.
    SWire
  | -- | Box with a label, a number of input ports and a number of output
    -- ports.
    SBox String Int Int
  | -- | Spider node with an input arity and an output arity (hypergraph
    -- junction: all its ports share one wire class).
    SSpider Int Int
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
  | -- | Left unitor @I ⊗ A -> A@.
    SUnitL
  | -- | Inverse left unitor @A -> I ⊗ A@.
    SUnitL'
  | -- | Right unitor @A ⊗ I -> A@.
    SUnitR
  | -- | Inverse right unitor @A -> A ⊗ I@.
    SUnitR'
  | -- | Associator @A ⊗ (B ⊗ C) -> (A ⊗ B) ⊗ C@.
    SAssoc
  | -- | Inverse associator @(A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C)@.
    SAssoc'
  | -- | Symmetric braiding @A ⊗ B -> B ⊗ A@.
    SSwap
  | -- | Trace: hide the last input/output pair as a feedback loop.
    --
    -- A value @STrace d@ represents a diagram @d@ whose last input and last
    -- output are connected, removing one port from each boundary.
    STrace SDiagram
  deriving (Eq, Show)

-- | Copy spider: one input forked to two outputs.
sCopy :: SDiagram
sCopy = SSpider 1 2

-- | Merge spider: two inputs joined to one output.
sMerge :: SDiagram
sMerge = SSpider 2 1

-- | Delete spider: erases one input.
sDelete :: SDiagram
sDelete = SSpider 1 0

-- | Create spider: produces one output from nothing.
sCreate :: SDiagram
sCreate = SSpider 0 1
