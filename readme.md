# string-diagrams

> String-diagram surface syntax and polynomial applications for circuits.

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

The package is one machinery pipeline with no deviation:

1. **Polynomial functors** (`Circuit.Poly`).
   Objects are interfaces `p(y) = Σ_i y^(Dir p i)` — a position together with
   a direction space.  This is the natural object language for open systems:
   a mode or shape, plus the request each mode makes of the world.

2. **Dependent lenses** (`Circuit.Poly`).
   Morphisms are dependent lenses: a forward map on positions and a backward
   map on directions.  This is the same shape that appears in open games,
   backpropagation (反向传播), differentiable programming, and categorical
   systems theory.

   Note the gap between the English stems and the Chinese term: 反向传播 is
   literally "backwards propagation", not "reverse-mode differentiation" or
   "automatic differentiation".  The string-diagram picture makes the
   backward pass visible as a literal right-to-left flow, so the Chinese name
   is closer to the geometry than the English jargon.

3. **The Int construction** (`Circuit.Poly.Int`).
   The Int construction turns a traced monoidal category into a compact
   closed category.  For polynomial lenses this means every wire becomes a
   pair: a forward type and a backward type.  Composition runs the forward
   pass left-to-right and the backward pass right-to-left.  Bending a wire
   back lets an output feed into an input — the categorical trace made
   concrete.

4. **String diagrams** (`Circuit.Poly.StringDiagram`).
   A deep-embedded DSL for drawing the morphisms above.  Every value
   remembers how it was built, so the same diagram can be interpreted as an
   executable `IntMorph` or rendered as an SVG via `strings-svg`.

The pipeline is natural: polynomials give the objects, lenses give the
morphisms, the Int construction gives feedback, and string diagrams give the
user-facing notation.  There is no point in the chain where you would rather
leave string diagrams behind — the pictures are the syntax.

(Dependent types are different.  If we put dependent types here we would also
leave strings, because dependent types want explicit indices and proof terms,
not wire-and-box pictures.  This library stays in the polynomial/string
world.)

## Why `string-diagrams`

`circuits-int` named only the middle engine, and `circuits-poly` named the
polynomial substrate.  Now that the polynomial core lives in `circuits`, this
package is the user-facing grammar layer: string diagrams and related
polynomial applications built on top of the semantic machinery.

```
string-diagrams  =  String diagrams
                  +  Spans
                  +  Int corridor
                  +  Differential polynomials
```

## A quick diagram

```haskell
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
- `string-diagrams` — this package: polynomial lenses, the Int corridor, and the
  string-diagram surface syntax.
- `strings-svg` — renders the `SDiagram` sketches as SVG equality galleries.
- `circuits-ad` — automatic differentiation for lenses.
- `process-stats` — statistical boxes built on `Circuit.Process` (the arrow
  formerly hand-rolled in `mealy`).

## Status

Experimental.  The string-diagram renderer currently handles boxes, wires,
swaps, cups and caps.  Multi-port "spider" nodes — the `copy`/`plus`
generators that caused the original bialgebra bug — are the next extension
needed so that the renderer can draw the laws it is supposed to explain.
