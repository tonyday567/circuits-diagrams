# circuits-int

> String diagrams for polynomial functors and the Int construction.

This library grew out of a bug.

We were writing oracle tests for `Circuit.FinRel`, checking that copy and plus
satisfy the bialgebra law:

```haskell
copy . plus == par plus plus . swapBlocks . par copy copy
```

The left-hand side merges two inputs and splits the result.  The right-hand
side copies each input, swaps the two middle blocks, and adds the pairs.  It
is a picture before it is an equation.  But we wrote it as a permutation on
wire indices:

```haskell
swapMiddle2 = wiring perm
  where
    perm 2 = 4
    perm 4 = 2
    perm i = i
```

For `n=1` it passed.  For `n=2` it failed.  The bug was obvious the moment we
drew the diagram: we had swapped two individual wires instead of two
`n`-wire blocks.  The `n=1` case was too degenerate to notice because a block
of size one looks like a single wire.

That is what this library is for: turning the pictures that make category
theory obvious into typed, executable Haskell.

## What is here

The package has three layers:

1. **Polynomial functors and dependent lenses** (`Circuit.Poly`).
   Objects are interfaces `p(y) = Σ_i y^(Dir p i)` — a position together with
   a direction space.  Morphisms are dependent lenses: a forward map on
   positions and a backward map on directions.  This is the same shape that
   appears in open games, backpropagation, differentiable programming, and
   categorical systems theory.

2. **The Int construction** (`Circuit.Int`).
   The Int construction turns a traced monoidal category into a compact
   closed category.  For our polynomial lenses this means every wire becomes
   a pair: a forward type and a backward type.  Composition runs the forward
   pass left-to-right and the backward pass right-to-left.  Bending a wire
   back lets an output feed into an input — the categorical trace made
   concrete.

3. **String diagrams** (`Circuit.Int.StringDiagram`).
   A deep-embedded DSL for drawing the morphisms in (1) and (2).  Every
   value remembers how it was built, so the same diagram can be interpreted
   as an executable `IntMorph` or rendered as an SVG via `strings-svg`.

## Why the name is awkward

`circuits-int` names only the middle layer.  The point of the library is not
the Int construction by itself; the point is that polynomials give you the
objects, lenses give you the morphisms, the Int construction gives you the
compact-closed feedback structure, and string diagrams give you the
user-facing notation.  If we were naming it today we might call it
`circuits-poly` or `circuits-diagram`, because Poly and the diagram syntax are
the entry points, while Int is the engine underneath.

For now the package keeps the old name to avoid churn downstream, but think
of it as:

```
circuits-int  =  Polynomial interfaces  +  Dependent lenses  +  Int corridor  +  String diagrams
```

## A quick diagram

```
-- feedback loop around a box f
knotTrace :: SDiagram
knotTrace =
  SThenD
    SBend'
    (SThenD (SBeside (SBox "f") SWire) SBend)
```

That code draws a wire leaving the unit, travelling through a box, and
bending back to disappear into the unit.  In `Circuit.FinRel` the same shape
is computed by `traceFinRel`, which eliminates the loop with a nullspace
calculation.  The picture tells you what the linear algebra is doing.

## Relationship to other packages

- `circuits` — the base category language: `Category`, `Tensor`, `Channel`,
  `Traced`, `CopyDiscard`, `MergeZero`.
- `circuits-int` — this package: polynomial lenses, the Int corridor, and the
  string-diagram surface syntax.
- `strings-svg` — renders the `SDiagram` sketches as SVG equality galleries.
- `circuits-ad`, `mealy` — concrete interpretations of lenses as automatic
  differentiation and state machines.

## Status

Experimental.  The string-diagram renderer currently handles boxes, wires,
swaps, cups and caps.  Multi-port "spider" nodes — the `copy`/`plus`
generators that caused the original bialgebra bug — are the next extension
needed so that the renderer can draw the laws it is supposed to explain.
