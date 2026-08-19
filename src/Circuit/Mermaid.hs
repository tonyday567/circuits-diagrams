-- | Mermaid printer for the string-diagram skeleton.
--
-- Test-only pin: emit an 'SDiagram' as a mermaid @flowchart@ so diagrams
-- render anywhere markdown does (org/emacs, GitHub), before any chart-svg
-- layout work.  The printer consumes the hypergraph normal form ("Circuit.Diagram.Hyper"), so spiders and swaps vanish into
-- port connectivity and structural laws show up as plain edges — a
-- copy-then-merge round trip prints as a single wire.
--
-- Design notes:
--
-- * One mermaid node per 'HyperNode'; structural constructors print as
--   symbols (@∪@, @∩@, @λ@, @α@, …).
-- * Boundary ports print as stadium nodes @in N@ / @out N@.
-- * A wire class with several producers or consumers fans out into one
--   mermaid edge per producer–consumer pair.
-- * Edges carry port labels only when a node endpoint has arity greater
--   than one.
-- * 'STurn' swaps node input/output arities, toggles a @†@ suffix on
--   labels, and reverses boundary order; node identity is by label, as in
--   the hypergraph normal form: two boxes with the same label collapse to
--   one mermaid node.
module Circuit.Mermaid
  ( toMermaid,
  )
where

import Circuit.Diagram (SDiagram)
import Circuit.Diagram.Hyper
  ( BoundaryEnd (..),
    HyperGraph (..),
    HyperNode (..),
    PortDir (..),
    PortEnd (..),
    Wire (..),
    normalise,
  )
import Data.List (nub)
import Prelude

-- $setup
-- >>> import Circuit.Mermaid
-- >>> import Circuit.Poly.StringDiagram

-- | Print a diagram skeleton as a mermaid flowchart.
--
-- >>> putStr (toMermaid (SThenD (SBox "f" 1 1) (SBox "g" 1 1)))
-- flowchart LR
--   in0(["in 0"])
--   out0(["out 0"])
--   n0["f"]
--   n1["g"]
--   n0 --> n1
--   in0 --> n0
--   n1 --> out0
--
-- Spiders are connectivity, so copy-then-merge is a single wire:
--
-- >>> putStr (toMermaid (SThenD sCopy sMerge))
-- flowchart LR
--   in0(["in 0"])
--   out0(["out 0"])
--   in0 --> out0
--
-- A cup is a two-input symbol node with labelled ports:
--
-- >>> putStr (toMermaid SBend)
-- flowchart LR
--   in0(["in 0"])
--   in1(["in 1"])
--   n0["∪"]
--   in0 -->|i0| n0
--   in1 -->|i1| n0
--
-- A trace hides the last input/output pair as a feedback loop:
--
-- >>> putStr (toMermaid (STrace (SBox "f" 2 2)))
-- flowchart LR
--   in0(["in 0"])
--   out0(["out 0"])
--   n0["f"]
--   n0 -->|o1:i1| n0
--   in0 -->|i0| n0
--   n0 -->|o0| out0
toMermaid :: SDiagram -> String
toMermaid = render . normalise

-- Print a hypergraph normal form as a mermaid flowchart.
render :: HyperGraph -> String
render hg =
  unlines $
    ["flowchart LR"]
      ++ fmap inDecl [0 .. hgInArity hg - 1]
      ++ fmap outDecl [0 .. hgOutArity hg - 1]
      ++ fmap nodeDecl nodes
      ++ concatMap wireEdges (hgWires hg)
  where
    nodes = nub (hgNodes hg)
    nodeIdOf lbl = "n" ++ show (idxOf lbl)
    idxOf lbl = case [i | (i, n) <- zip [(0 :: Int) ..] nodes, hnLabel n == lbl] of
      (i : _) -> i
      [] -> error "render: port references unknown node"
    arityOf lbl = case [n | n <- nodes, hnLabel n == lbl] of
      (n : _) -> n
      [] -> error "render: port references unknown node"

    inDecl i = "  in" ++ show i ++ "([\"in " ++ show i ++ "\"])"
    outDecl i = "  out" ++ show i ++ "([\"out " ++ show i ++ "\"])"
    nodeDecl n = "  " ++ nodeIdOf (hnLabel n) ++ shape (hnLabel n)

    shape lbl = case lbl of
      "cup" -> "[\"∪\"]"
      "cap" -> "[\"∩\"]"
      "unitL" -> "[\"λ\"]"
      "unitL'" -> "[\"λ⁻¹\"]"
      "unitR" -> "[\"ρ\"]"
      "unitR'" -> "[\"ρ⁻¹\"]"
      "assoc" -> "[\"α\"]"
      "assoc'" -> "[\"α⁻¹\"]"
      "prism" -> "{{prism}}"
      _ -> "[\"" ++ escape lbl ++ "\"]"

    escape = fmap (\c -> if c == '"' then '\'' else c)

    -- producers point right: boundary inputs and node output ports
    producers w =
      [Left i | InB i <- wBoundary w]
        ++ [Right p | p@(PortEnd _ Out _) <- wPorts w]
    -- consumers point left: boundary outputs and node input ports
    consumers w =
      [Left i | OutB i <- wBoundary w]
        ++ [Right p | p@(PortEnd _ In _) <- wPorts w]

    endName (Left i) = "in" ++ show i
    endName (Right (PortEnd lbl _ _)) = nodeIdOf lbl

    outEndName (Left i) = "out" ++ show i
    outEndName (Right (PortEnd lbl _ _)) = nodeIdOf lbl

    portLabel p c =
      case (p, c) of
        (Right (PortEnd sl _ si), Right (PortEnd tl _ ti))
          | hnOutArity (arityOf sl) > 1 || hnInArity (arityOf tl) > 1 ->
              Just ("o" ++ show si ++ ":i" ++ show ti)
        (Right (PortEnd sl _ si), Left _)
          | hnOutArity (arityOf sl) > 1 ->
              Just ("o" ++ show si)
        (Left _, Right (PortEnd tl _ ti))
          | hnInArity (arityOf tl) > 1 ->
              Just ("i" ++ show ti)
        _ -> Nothing

    wireEdges w =
      [ "  " ++ endName p ++ edgeLabel (portLabel p c) ++ outEndName c
      | p <- producers w,
        c <- consumers w
      ]

    edgeLabel Nothing = " --> "
    edgeLabel (Just t) = " -->|" ++ t ++ "| "
