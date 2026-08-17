{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Port-aware layout of untyped string diagrams ('SDiagram').
--
-- Coordinates use chart-svg data space (y increases upward).  Morphisms
-- compose left-to-right ('SThenD'); tensor stacks top-to-bottom
-- ('SBeside').  That matches the left/right port model and the wall-chart
-- schematics — not the wording slip in the requirements bullet that had
-- composition stacking vertically.
--
-- Every primitive emits its boundary ports on a uniform vertical grid
-- with 'portPitch' spacing, so 'thenL' aligns whole port lists pairwise
-- and 'besideL' concatenates port lists slot by slot.  A port-count
-- mismatch in 'thenL' is a wiring error: the connection is truncated to
-- the common prefix and each unmatched port is marked with a dangling
-- stub and dot, so the error is visible rather than silent.
module Strings.Svg.Layout
  ( Layout (..),
    layoutSDiagram,
    layoutWidth,
    layoutHeight,
    moveLayout,
    countCharts,
    countLines,
    countRects,
    countPaths,
    countGlyphs,
    unitW,
    boxH,
    composeGap,
    tensorGap,
    portPitch,
  )
where

import Chart
import Circuit.Poly.StringDiagram (SDiagram (..))
import Data.Text (pack)
import Optics.Core
import Strings.Svg.Palette
import Prelude

-- | Laid-out diagram with boundary ports and bounding box.
data Layout = Layout
  { picture :: ChartTree,
    leftPorts :: [Point Double],
    rightPorts :: [Point Double],
    bounds :: Rect Double
  }
  deriving (Eq, Show)

-- | Horizontal span of one wire / box cell.
unitW :: Double
unitW = 1.0

-- | Box height (centred on the wire).
boxH :: Double
boxH = 0.6

-- | Gap between sequential (then) cells.
composeGap :: Double
composeGap = 0.12

-- | Gap between tensor (beside) cells.
tensorGap :: Double
tensorGap = 0.35

-- | Vertical pitch between parallel wires.
portPitch :: Double
portPitch = 0.5

layoutWidth :: Layout -> Double
layoutWidth (Layout _ _ _ (Rect x z _ _)) = z - x

layoutHeight :: Layout -> Double
layoutHeight (Layout _ _ _ (Rect _ _ y w)) = w - y

-- | Translate a layout by a vector.
moveLayout :: Point Double -> Layout -> Layout
moveLayout d (Layout pic ls rs b) =
  Layout
    { picture = moveChartTree d pic,
      leftPorts = (d +) <$> ls,
      rightPorts = (d +) <$> rs,
      bounds = addPoint d b
    }

-- | chart-svg has no public moveChartTree reexport path that keeps names;
-- fold charts with moveChart.
moveChartTree :: Point Double -> ChartTree -> ChartTree
moveChartTree d = over charts' (fmap (moveChart d))

-- | Layout an untyped skeleton at the origin (first left port near @x=0@).
layoutSDiagram :: SDiagram -> Layout
layoutSDiagram = go 0
  where
    -- box colour index cycles blue / magenta for multi-box composites
    go :: Int -> SDiagram -> Layout
    go n = \case
      SWire -> wireL
      SBox lbl m o -> boxL n lbl m o
      SSpider m o -> spiderL m o
      SPrismBox -> boxL n "prism" 1 1
      SBeside a b -> besideL (go n a) (go (n + boxCount a) b)
      SThenD a b -> thenL (go n a) (go (n + boxCount a) b)
      SBend -> cupL
      SBend' -> capL
      STurn d -> turnL (go n d)
      SUnitL -> wireL
      SUnitL' -> wireL
      SUnitR -> wireL
      SUnitR' -> wireL
      SAssoc -> multiWireL 3
      SAssoc' -> multiWireL 3
      SSwap -> swapL

boxCount :: SDiagram -> Int
boxCount = \case
  SBox _ _ _ -> 1
  SPrismBox -> 1
  SBeside a b -> boxCount a + boxCount b
  SThenD a b -> boxCount a + boxCount b
  STurn d -> boxCount d
  _ -> 0

boxStroke :: Int -> Colour
boxStroke n = case n `mod` 3 of
  0 -> accentBlue
  1 -> accentMagenta
  _ -> accentGreen

--------------------------------------------------------------------------------
-- primitives
--------------------------------------------------------------------------------

wireL :: Layout
wireL =
  Layout
    { picture = unnamed [LineChart (wireStyle wireGrey) [[Point 0 0, Point unitW 0]]],
      leftPorts = [Point 0 0],
      rightPorts = [Point unitW 0],
      bounds = Rect 0 unitW (-0.05) 0.05
    }

-- | @k@ parallel identity wires spanning one unit of width.
multiWireL :: Int -> Layout
multiWireL k =
  Layout
    { picture = unnamed lines',
      leftPorts = ports,
      rightPorts = (Point unitW 0 +) <$> ports0,
      bounds = Rect 0 unitW (ymin - 0.05) (ymax + 0.05)
    }
  where
    ports0 = portYs k
    ports = ports0
    lines' =
      [ LineChart (wireStyle wireGrey) [[p, p + Point unitW 0]]
      | p <- ports0
      ]
    ys = (\(Point _ y) -> y) <$> ports0
    ymin = minimum (0 : ys)
    ymax = maximum (0 : ys)

portYs :: Int -> [Point Double]
portYs k
  | k <= 0 = []
  | k == 1 = [Point 0 0]
  | otherwise =
      let half = fromIntegral (k - 1) * portPitch / 2
       in [Point 0 (half - fromIntegral i * portPitch) | i <- [0 .. k - 1]]

-- | Box with @m@ input ports on the left edge and @n@ output ports on
-- the right edge.  Ports sit on the uniform 'portPitch' grid; short
-- stubs connect each boundary port to a pad dot on the box edge, and the
-- box height grows to fit @max m n@ ports.  A one-port box keeps the
-- classic look: a single centred stub per side, no pad dots.
boxL :: Int -> String -> Int -> Int -> Layout
boxL c lbl m n =
  Layout
    { picture =
        unnamed
          ( [ LineChart (wireStyle wireGrey) [[Point 0 y, Point x0 y]]
            | y <- inYs
            ]
              ++ [ LineChart (wireStyle wireGrey) [[Point x1 y, Point unitW y]]
                 | y <- outYs
                 ]
              ++ [ RectChart (boxStyle (boxStroke c)) [Rect x0 x1 (-h2) h2],
                   TextChart labelStyle [(pack lbl, Point midX 0)]
                 ]
              ++ pads
          ),
      leftPorts = [Point 0 y | y <- inYs],
      rightPorts = [Point unitW y | y <- outYs],
      bounds = Rect 0 unitW (-h2 - 0.05) (h2 + 0.05)
    }
  where
    inYs = [y | Point _ y <- portYs (max 0 m)]
    outYs = [y | Point _ y <- portYs (max 0 n)]
    padHalf = maximum (0 : [max y (-y) | y <- inYs ++ outYs])
    h2 = max (boxH / 2) (padHalf + padMargin)
    padMargin = 0.18
    x0 = 0.18
    x1 = unitW - 0.18
    midX = (x0 + x1) / 2
    pads
      | max m n > 1 =
          [ GlyphChart
              (dotStyle 0.06 (boxStroke c))
              ([Point x0 y | y <- inYs] ++ [Point x1 y | y <- outYs])
          ]
      | otherwise = []

-- | Spider: a junction dot with @m@ input legs converging from the left
-- and @n@ output legs diverging to the right, drawn as smooth cubics
-- with horizontal tangents.  'SSpider' 1 2 and 'SSpider' 2 1 are the
-- classic copy\/merge forks; the degenerate arities are terminators —
-- 'SSpider' 1 0 a stub ending in a dot, 'SSpider' 0 1 a dot opening
-- into a stub, 'SSpider' 0 0 a bare dot.
spiderL :: Int -> Int -> Layout
spiderL m n =
  Layout
    { picture =
        unnamed
          ( [ PathChart
                (pathStroke wireGrey 0.035)
                [StartP p, CubicP (p + Point leg 0) (c - Point leg 0) c]
            | p <- lefts
            ]
              ++ [ PathChart
                     (pathStroke wireGrey 0.035)
                     [StartP c, CubicP (c + Point leg 0) (p - Point leg 0) p]
                 | p <- rights
                 ]
              ++ [GlyphChart (dotStyle 0.12 accentBlue) [c]]
          ),
      leftPorts = lefts,
      rightPorts = rights,
      bounds = Rect 0 unitW (ymin - 0.05) (ymax + 0.05)
    }
  where
    c = Point (unitW / 2) 0
    leg = 0.18
    lefts = portYs (max 0 m)
    rights = (Point unitW 0 +) <$> portYs (max 0 n)
    ys = [y | Point _ y <- lefts ++ rights]
    ymin = minimum (0 : ys)
    ymax = maximum (0 : ys)

-- | Small filled circle style (spider dots, port pads, error markers).
dotStyle :: Double -> Colour -> Style
dotStyle s c =
  defaultGlyphStyle
    & set #glyphShape CircleGlyph
    & set #size s
    & set #color c
    & set #borderColor c
    & set #borderSize 0.02
    & set #scaleP NoScaleP

-- | Cup (counit): two inputs, closes on the right.
cupL :: Layout
cupL =
  Layout
    { picture =
        unnamed
          [ PathChart
              (pathStroke accentBlue 0.04)
              [ StartP (Point 0 top),
                CubicP (Point 0.55 top) (Point 0.55 bot) (Point 0 bot)
              ]
          ],
      leftPorts = [Point 0 top, Point 0 bot],
      rightPorts = [],
      bounds = Rect 0 0.6 (bot - 0.05) (top + 0.05)
    }
  where
    top = portPitch / 2
    bot = -(portPitch / 2)

-- | Cap (unit): opens on the left into two outputs.
capL :: Layout
capL =
  Layout
    { picture =
        unnamed
          [ PathChart
              (pathStroke accentBlue 0.04)
              [ StartP (Point unitW top),
                CubicP (Point 0.45 top) (Point 0.45 bot) (Point unitW bot)
              ]
          ],
      leftPorts = [],
      rightPorts = [Point unitW top, Point unitW bot],
      bounds = Rect 0.4 unitW (bot - 0.05) (top + 0.05)
    }
  where
    top = portPitch / 2
    bot = -(portPitch / 2)

-- | Braid: under-strand continuous; over-strand gapped at the crossing.
swapL :: Layout
swapL =
  Layout
    { picture =
        unnamed
          [ -- under (magenta): bottom-left → top-right continuous
            LineChart (wireStyle accentMagenta) [[Point 0 bot, Point unitW top]],
            -- over (blue): top-left → bottom-right with gap
            LineChart (wireStyle accentBlue) [[Point 0 top, Point (cx - gap) (cy + gapY)]],
            LineChart (wireStyle accentBlue) [[Point (cx + gap) (cy - gapY), Point unitW bot]]
          ],
      leftPorts = [Point 0 top, Point 0 bot],
      rightPorts = [Point unitW top, Point unitW bot],
      bounds = Rect 0 unitW (bot - 0.05) (top + 0.05)
    }
  where
    top = portPitch / 2
    bot = -(portPitch / 2)
    cx = unitW / 2
    cy = 0
    gap = 0.08
    gapY = gap * (top - bot) / unitW

--------------------------------------------------------------------------------
-- composition
--------------------------------------------------------------------------------

-- | Sequential composition: @a@ then @b@ (left to right).
--
-- The whole port list is aligned pairwise: @b@ is shifted so that its
-- first input port meets @a@'s first output port, and since every
-- primitive emits ports on the uniform 'portPitch' grid, equal-length
-- port lists then line up exactly.  A port-count mismatch is a wiring
-- error; layout stays total by truncating the connection to the common
-- prefix and marking each unmatched port with a dangling stub and dot
-- ('danglingPorts'), so the error is visible rather than silent.
thenL :: Layout -> Layout -> Layout
thenL a b =
  Layout
    { picture = group Nothing [picture a, picture b', connectors, dangling],
      leftPorts = leftPorts a,
      rightPorts = rightPorts b',
      bounds = bounds a <> bounds b' <> connBounds
    }
  where
    -- align b so its left ports match a's right ports (first port vertical align)
    dy = alignY (rightPorts a) (leftPorts b)
    dx = rx a + composeGap - lx b
    b' = moveLayout (Point dx dy) b
    outs = rightPorts a
    ins = leftPorts b'
    connectors = connectPorts outs ins
    dangling =
      danglingPorts (drop (length ins) outs) 1
        <> danglingPorts (drop (length outs) ins) (-1)
    connBounds =
      case outs <> ins <> danglingEnds of
        [] -> Rect 0 0 0 0
        (p0 : ps) ->
          foldl
            (<>)
            (let Point x y = p0 in Rect x x y y)
            [let Point x y = p in Rect x x y y | p <- ps]
    danglingEnds =
      [p + Point stub 0 | p <- drop (length ins) outs]
        ++ [p - Point stub 0 | p <- drop (length outs) ins]
    stub = 0.15

-- | Visible wiring-error markers: a short stub continuing past an
-- unmatched port, ending in a magenta dot.  The 'Double' is the stub
-- direction (+1 to the right, -1 to the left).
danglingPorts :: [Point Double] -> Double -> ChartTree
danglingPorts ps dir =
  unnamed
    ( [ LineChart (wireStyle accentMagenta) [[p, p + Point (dir * stub) 0]]
      | p <- ps
      ]
        ++ [ GlyphChart (dotStyle 0.08 accentMagenta) [p + Point (dir * stub) 0 | p <- ps]
           | not (null ps)
           ]
    )
  where
    stub = 0.15

-- | Tensor: @a@ above @b@ (ports concatenated top-then-bottom).
--
-- When both sides have boundary ports, each is placed on a shared
-- vertical slot grid with 'portPitch' spacing: @a@ takes the top slots,
-- @b@ the next ones, so the concatenated port lists stay in vertical
-- order at a uniform pitch and downstream composition connects straight.
-- Each side anchors on its first left port (first right port when it has
-- no left ports) and moves rigidly, so internal wires stretch with their
-- diagram and nothing is rerouted across a box body.  Diagrams without
-- boundary ports fall back to bounding-box stacking with 'tensorGap'.
besideL :: Layout -> Layout -> Layout
besideL a b
  | slots a > 0 && slots b > 0 = gridBeside a b
  | otherwise = boxBeside a b

-- | Slot-grid tensor: both sides share a uniform 'portPitch' grid.
gridBeside :: Layout -> Layout -> Layout
gridBeside a b =
  Layout
    { picture = group Nothing [picture a', picture b'],
      leftPorts = leftPorts a' <> leftPorts b',
      rightPorts = rightPorts a' <> rightPorts b',
      bounds = bounds a' <> bounds b'
    }
  where
    half = fromIntegral (slots a + slots b - 1) * portPitch / 2
    slotY i = half - fromIntegral i * portPitch
    a' = moveLayout (Point (-lx a) (slotY 0 - anchorY a)) a
    b' = moveLayout (Point (-lx b) (slotY (slots a) - anchorY b)) b

-- | Bounding-box tensor: fallback for port-less diagrams.
boxBeside :: Layout -> Layout -> Layout
boxBeside a b =
  Layout
    { picture = group Nothing [picture a', picture b'],
      leftPorts = leftPorts a' <> leftPorts b',
      rightPorts = rightPorts a' <> rightPorts b',
      bounds = bounds a' <> bounds b'
    }
  where
    -- place a above b with tensorGap between bounding boxes
    ay = -(midY a) + layoutHeight a / 2 + tensorGap / 2
    by = -(midY b) - layoutHeight b / 2 - tensorGap / 2
    a' = moveLayout (Point (-lx a) ay) a
    b' = moveLayout (Point (-lx b) by) b

-- | Boundary slot count of a layout: the larger port-list length.
slots :: Layout -> Int
slots l = max (length (leftPorts l)) (length (rightPorts l))

-- | Vertical anchor of a layout: its first left port, or its first right
-- port when it has no left ports.
anchorY :: Layout -> Double
anchorY l = case leftPorts l of
  (Point _ y : _) -> y
  [] -> case rightPorts l of
    (Point _ y : _) -> y
    [] -> 0

turnL :: Layout -> Layout
turnL lay =
  Layout
    { picture = over charts' (fmap (rotateChartData pi c)) (picture lay),
      -- dual: old right becomes left, reversed; old left becomes right, reversed
      leftPorts = reverse (reflect <$> rightPorts lay),
      rightPorts = reverse (reflect <$> leftPorts lay),
      bounds = reflectRect (bounds lay)
    }
  where
    c = centre (bounds lay)
    reflect (Point x y) =
      let Point cx cy = c
       in Point (2 * cx - x) (2 * cy - y)
    reflectRect (Rect x z y w) =
      let Point cx cy = c
       in Rect (2 * cx - z) (2 * cx - x) (2 * cy - w) (2 * cy - y)

--------------------------------------------------------------------------------
-- helpers
--------------------------------------------------------------------------------

lx :: Layout -> Double
lx (Layout _ _ _ (Rect x _ _ _)) = x

rx :: Layout -> Double
rx (Layout _ _ _ (Rect _ z _ _)) = z

midY :: Layout -> Double
midY (Layout _ _ _ (Rect _ _ y w)) = (y + w) / 2

centre :: Rect Double -> Point Double
centre (Rect x z y w) = Point ((x + z) / 2) ((y + w) / 2)

alignY :: [Point Double] -> [Point Double] -> Double
alignY (Point _ ya : _) (Point _ yb : _) = ya - yb
alignY _ _ = 0

connectPorts :: [Point Double] -> [Point Double] -> ChartTree
connectPorts as bs =
  unnamed
    [ LineChart (wireStyle wireGrey) [[p, q]]
    | (p, q) <- zip as bs,
      p /= q
    ]

rotateChartData :: Double -> Point Double -> Chart -> Chart
rotateChartData theta c = over #chartData (rotateData theta c)

rotateData :: Double -> Point Double -> ChartData -> ChartData
rotateData theta c = \case
  RectData rs -> RectData (fmap (rotateRect theta c) rs)
  LineData lss -> LineData (fmap (fmap (rotatePoint theta c)) lss)
  GlyphData ps -> GlyphData (fmap (rotatePoint theta c) ps)
  TextData ts -> TextData (fmap (fmap (rotatePoint theta c)) ts)
  PathData ps -> PathData (fmap (rotatePath theta c) ps)
  BlankData rs -> BlankData (fmap (rotateRect theta c) rs)

rotatePoint :: Double -> Point Double -> Point Double -> Point Double
rotatePoint theta (Point cx cy) (Point x y) =
  let dx = x - cx
      dy = y - cy
      ct = cos theta
      st = sin theta
   in Point (cx + ct * dx - st * dy) (cy + st * dx + ct * dy)

rotateRect :: Double -> Point Double -> Rect Double -> Rect Double
rotateRect theta c (Rect x z y w) =
  let corners = [Point x y, Point z y, Point x w, Point z w]
      cs = rotatePoint theta c <$> corners
      xs = (\(Point px _) -> px) <$> cs
      ys = (\(Point _ py) -> py) <$> cs
   in Rect (minimum xs) (maximum xs) (minimum ys) (maximum ys)

rotatePath :: Double -> Point Double -> PathData Double -> PathData Double
rotatePath theta c = \case
  StartP p -> StartP (rotatePoint theta c p)
  LineP p -> LineP (rotatePoint theta c p)
  CubicP a b p -> CubicP (rotatePoint theta c a) (rotatePoint theta c b) (rotatePoint theta c p)
  QuadP a p -> QuadP (rotatePoint theta c a) (rotatePoint theta c p)
  ArcP i p -> ArcP i (rotatePoint theta c p)

--------------------------------------------------------------------------------
-- structural counts
--------------------------------------------------------------------------------

countCharts :: Layout -> Int
countCharts = length . foldOf charts' . picture

countLines :: Layout -> Int
countLines = countPred isLine
  where
    isLine (Chart _ (LineData _)) = True
    isLine _ = False

countRects :: Layout -> Int
countRects = countPred isRect
  where
    isRect (Chart _ (RectData _)) = True
    isRect _ = False

countPaths :: Layout -> Int
countPaths = countPred isPath
  where
    isPath (Chart _ (PathData _)) = True
    isPath _ = False

-- | Glyph charts (spider dots, port pads, wiring-error markers).
countGlyphs :: Layout -> Int
countGlyphs = countPred isGlyph
  where
    isGlyph (Chart _ (GlyphData _)) = True
    isGlyph _ = False

countPred :: (Chart -> Bool) -> Layout -> Int
countPred p = length . filter p . foldOf charts' . picture
