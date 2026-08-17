-- | Hypergraph normal form for the drawing-level hyper fragment of
-- 'SDiagram' ('SWire', 'SSpider', multi-port 'SBox', 'SBeside', 'SThenD',
-- 'SSwap').
--
-- A diagram is interpreted as port connectivity: every node port and
-- every boundary port is a port reference, and a union-find over those
-- references quotients them into wire classes.  Spiders contribute no
-- node — they simply merge the classes of all their ports, so spider
-- fusion (and hence the bialgebra and spider laws) is automatic, and
-- diagrams that differ only in tree shape normalise to the same value.
-- Constructors outside the hyper fragment (cups, caps, unitors, …) are
-- treated as opaque nodes with their natural port arities.
--
-- This is not a full graph-isomorphism check: node ports are keyed by
-- box label, so two boxes carrying the same label are interchangeable.
-- That is exact for the oracle suite and cheap; revisit if unlabelled
-- node isomorphism ever matters.
module Circuit.Diagram.Hyper
  ( HyperGraph (..),
    HyperNode (..),
    Wire (..),
    BoundaryEnd (..),
    PortEnd (..),
    PortDir (..),
    normalise,
    hyperEquiv,
    arity,
  )
where

import Circuit.Diagram (SDiagram (..))
import Data.List (foldl', groupBy, sort, sortOn)
import Prelude

-- | A diagram as port connectivity: boundary arities, a sorted multiset
-- of nodes, and the wires (equivalence classes of ports).
data HyperGraph = HyperGraph
  { -- | Number of input (left boundary) ports.
    hgInArity :: Int,
    -- | Number of output (right boundary) ports.
    hgOutArity :: Int,
    -- | Sorted nodes.
    hgNodes :: [HyperNode],
    -- | Sorted wires.
    hgWires :: [Wire]
  }
  deriving (Eq, Show)

-- | A box (or opaque constructor) with its port arities.
data HyperNode = HyperNode
  { hnLabel :: String,
    hnInArity :: Int,
    hnOutArity :: Int
  }
  deriving (Eq, Ord, Show)

-- | One wire class: the boundary ends and node ports it connects, each
-- sorted.
data Wire = Wire
  { wBoundary :: [BoundaryEnd],
    wPorts :: [PortEnd]
  }
  deriving (Eq, Ord, Show)

-- | A diagram boundary port.
data BoundaryEnd
  = -- | Input port (left boundary) at the given index.
    InB Int
  | -- | Output port (right boundary) at the given index.
    OutB Int
  deriving (Eq, Ord, Show)

-- | A node port: box label, direction and port index.
data PortEnd = PortEnd String PortDir Int
  deriving (Eq, Ord, Show)

-- | Whether a node port is an input or an output.
data PortDir = In | Out
  deriving (Eq, Ord, Show)

-- | Boundary port counts of a diagram: @(inputs, outputs)@.  The unit of
-- a unitor carries no wire, so unitors are @1 -> 1@.
arity :: SDiagram -> (Int, Int)
arity = \case
  SWire -> (1, 1)
  SBox _ m n -> (m, n)
  SSpider m n -> (m, n)
  SPrismBox -> (1, 1)
  SBeside f g ->
    let (fi, fo) = arity f
        (gi, go') = arity g
     in (fi + gi, fo + go')
  SThenD f g -> (fst (arity f), snd (arity g))
  SBend -> (2, 0)
  SBend' -> (0, 2)
  STurn d -> let (i, o) = arity d in (o, i)
  SUnitL -> (1, 1)
  SUnitL' -> (1, 1)
  SUnitR -> (1, 1)
  SUnitR' -> (1, 1)
  SAssoc -> (3, 3)
  SAssoc' -> (3, 3)
  SSwap -> (2, 2)
  STrace d ->
    let (i, o) = arity d
     in (i - 1, o - 1)

-- | Interpret a diagram as its hypergraph normal form.
--
-- Assumes composable diagrams ('SThenD' zips the inner ports and drops
-- any excess): the drawing syntax is untyped, so ill-formed composites
-- degrade to dangling ports rather than an error.
normalise :: SDiagram -> HyperGraph
normalise d =
  HyperGraph
    { hgInArity = length ins,
      hgOutArity = length outs,
      hgNodes =
        sort
          [ HyperNode lbl (length bins) (length bouts)
          | BuiltNode lbl bins bouts <- builtNodes b
          ],
      hgWires = sort (mkWire <$> classes)
    }
  where
    (b, (ins, outs)) = go d emptyBuild
    rootOf = findRoot (parent b)
    classes =
      groupBy
        (\e e' -> rootOf (fst e) == rootOf (fst e'))
        (sortOn (rootOf . fst) allEnds)
    allEnds =
      [(p, BoundaryE (InB ix)) | (ix, p) <- zip [0 ..] ins]
        ++ [(p, BoundaryE (OutB ix)) | (ix, p) <- zip [0 ..] outs]
        ++ [ (p, PortE (PortEnd lbl dir ix))
           | BuiltNode lbl bins bouts <- builtNodes b,
             (dir, ports) <- [(In, bins), (Out, bouts)],
             (ix, p) <- zip [0 ..] ports
           ]
    mkWire es =
      Wire
        (sort [e | (_, BoundaryE e) <- es])
        (sort [e | (_, PortE e) <- es])

-- | Structural equality of diagrams up to hypergraph connectivity.
hyperEquiv :: SDiagram -> SDiagram -> Bool
hyperEquiv f g = normalise f == normalise g

--------------------------------------------------------------------------------
-- build: union-find over port references
--------------------------------------------------------------------------------

-- | A node under construction, with its port references.
data BuiltNode = BuiltNode String [Int] [Int]

data Build = Build
  { nextPort :: Int,
    parent :: [(Int, Int)],
    builtNodes :: [BuiltNode]
  }

emptyBuild :: Build
emptyBuild = Build 0 [] []

fresh :: Build -> (Build, Int)
fresh b = (b {nextPort = nextPort b + 1}, nextPort b)

freshPorts :: Int -> Build -> (Build, [Int])
freshPorts n b0 = foldl' step (b0, []) [1 .. n]
  where
    step (b, ps) _ = let (b', p) = fresh b in (b', ps ++ [p])

findRoot :: [(Int, Int)] -> Int -> Int
findRoot ps p = case lookup p ps of
  Nothing -> p
  Just q -> findRoot ps q

-- | Merge the classes of two ports (first root wins, for determinism).
-- Ports already in the same class are left alone — recording the link
-- would create a self-loop.
unite :: Int -> Int -> Build -> Build
unite p q b =
  let rp = findRoot (parent b) p
      rq = findRoot (parent b) q
   in if rp == rq then b else b {parent = (rq, rp) : parent b}

addNode :: String -> [Int] -> [Int] -> Build -> Build
addNode lbl ins outs b = b {builtNodes = BuiltNode lbl ins outs : builtNodes b}

-- | An opaque node with the given port arities.
node :: String -> Int -> Int -> Build -> (Build, ([Int], [Int]))
node lbl m n b0 =
  let (b1, ins) = freshPorts m b0
      (b2, outs) = freshPorts n b1
   in (addNode lbl ins outs b2, (ins, outs))

-- | Traverse the tree, returning the boundary port references.
go :: SDiagram -> Build -> (Build, ([Int], [Int]))
go d b0 = case d of
  SWire ->
    let (b1, p) = fresh b0
        (b2, q) = fresh b1
     in (unite p q b2, ([p], [q]))
  SBox lbl m n -> node lbl m n b0
  SSpider m n ->
    let (b1, ins) = freshPorts m b0
        (b2, outs) = freshPorts n b1
        b3 = case ins ++ outs of
          [] -> b2
          (p : ps) -> foldl' (flip (unite p)) b2 ps
     in (b3, (ins, outs))
  SPrismBox -> node "prism" 1 1 b0
  SBeside f g ->
    let (b1, (fi, fo)) = go f b0
        (b2, (gi, go')) = go g b1
     in (b2, (fi ++ gi, fo ++ go'))
  SThenD f g ->
    let (b1, (fi, fo)) = go f b0
        (b2, (gi, go')) = go g b1
        b3 = foldl' (\bb (p, q) -> unite p q bb) b2 (zip fo gi)
     in (b3, (fi, go'))
  SBend -> node "cup" 2 0 b0
  SBend' -> node "cap" 0 2 b0
  STurn d' -> let (i, o) = arity d' in node "turn" o i b0
  SUnitL -> node "unitL" 1 1 b0
  SUnitL' -> node "unitL'" 1 1 b0
  SUnitR -> node "unitR" 1 1 b0
  SUnitR' -> node "unitR'" 1 1 b0
  SAssoc -> node "assoc" 3 3 b0
  SAssoc' -> node "assoc'" 3 3 b0
  SSwap ->
    let (b1, i0) = fresh b0
        (b2, i1) = fresh b1
        (b3, o0) = fresh b2
        (b4, o1) = fresh b3
     in (unite i0 o1 (unite i1 o0 b4), ([i0, i1], [o0, o1]))
  STrace d' ->
    let (b1, (ins, outs)) = go d' b0
        initLast xs = splitAt (length xs - 1) xs
     in case (initLast ins, initLast outs) of
          ((is, [i]), (os, [o])) -> (unite i o b1, (is, os))
          _ -> (b1, (ins, outs))

-- | A port end while grouping: either a boundary port or a node port.
data End = BoundaryE BoundaryEnd | PortE PortEnd
