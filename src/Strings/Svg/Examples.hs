{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The seven equality diagrams from the renderer order of record.
module Strings.Svg.Examples
  ( yankingRightExample,
    yankingLeftExample,
    slidingExample,
    traceSlidingExample,
    braidInverseExample,
    tensorInterchangeExample,
    starArdenExample,
    knotBraid3Example,
    knotCircleExample,
    knotTraceExample,
    knotTangleExample,
    allExamples,
    writeAllExamples,
  )
where

import Chart
import Circuit.Poly.StringDiagram (SDiagram (..), boxLabelled, skeleton)
import Circuit.Poly qualified as Poly
import Data.Text (pack)
import Optics.Core
import Strings.Svg.Layout
import Strings.Svg.Palette
import Strings.Svg.Render
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import Prelude

-- | Tiny labelled identity box (types discarded after 'skeleton').
boxF :: String -> SDiagram
boxF lbl = skeleton (boxLabelled lbl (Poly.lens id (\_ da -> da)))

-- | @a = b = c = …@ as a single row of layouts.
rowEquals :: [Layout] -> Layout
rowEquals [] = layoutSDiagram SWire
rowEquals (x : xs) = foldl equalityRow x xs

--------------------------------------------------------------------------------
-- 1. Right yanking
--------------------------------------------------------------------------------

-- | Cap–cup snake equals a straight wire.
yankingRightExample :: ChartOptions
yankingRightExample =
  renderLayout $
    equalityRow snake idWire
  where
    snake =
      layoutSDiagram $
        SThenD
          (SBeside SBend' SWire)
          (SBeside SWire SBend)
    idWire = layoutSDiagram SWire

--------------------------------------------------------------------------------
-- 2. Left yanking
--------------------------------------------------------------------------------

yankingLeftExample :: ChartOptions
yankingLeftExample =
  renderLayout $
    equalityRow snake idWire
  where
    snake =
      layoutSDiagram $
        SThenD
          (SBeside SWire SBend')
          (SBeside SBend SWire)
    idWire = layoutSDiagram SWire

--------------------------------------------------------------------------------
-- 3. Sliding: f;id = f = id;f
--------------------------------------------------------------------------------

slidingExample :: ChartOptions
slidingExample =
  renderLayout $
    rowEquals
      [ layoutSDiagram (SThenD (boxF "f") SWire),
        layoutSDiagram (boxF "f"),
        layoutSDiagram (SThenD SWire (boxF "f"))
      ]

--------------------------------------------------------------------------------
-- 4. Trace sliding: box outside feedback = box inside feedback
--------------------------------------------------------------------------------

traceSlidingExample :: ChartOptions
traceSlidingExample =
  renderLayout $
    equalityRow outside inside
  where
    -- feedback loop drawn as dashed cubic around a wire; box outside vs inside
    outside = feedbackWith (Just "f") False
    inside = feedbackWith (Just "f") True

-- | Simple feedback cartoon: through-wire plus a loop above.
-- When @boxInside@, the label sits on the loop; otherwise on the through-wire.
feedbackWith :: Maybe String -> Bool -> Layout
feedbackWith mlab boxInside =
  Layout
    { picture =
        unnamed $
          [ LineChart (wireStyle wireGrey) [[Point 0 0, Point 2 0]],
            PathChart
              ( pathStroke accentBlue 0.035
                  & set #dasharray (Just [0.08, 0.05])
              )
              [ StartP (Point 0.4 0),
                CubicP (Point 0.4 0.7) (Point 1.6 0.7) (Point 1.6 0),
                CubicP (Point 1.6 (-0.05)) (Point 0.4 (-0.05)) (Point 0.4 0)
              ]
          ]
            <> boxCharts,
      leftPorts = [Point 0 0],
      rightPorts = [Point 2 0],
      bounds = Rect 0 2 (-0.35) 0.85
    }
  where
    boxCharts = case mlab of
      Nothing -> []
      Just lbl ->
        let (cx, cy) = if boxInside then (1.0, 0.55) else (1.0, 0)
            hw = 0.28
            hh = 0.18
         in [ RectChart (boxStyle accentBlue) [Rect (cx - hw) (cx + hw) (cy - hh) (cy + hh)],
              TextChart labelStyle [(pack lbl, Point cx cy)]
            ]

--------------------------------------------------------------------------------
-- 5. Braid inverse: swap;swap = id⊗id
--------------------------------------------------------------------------------

braidInverseExample :: ChartOptions
braidInverseExample =
  renderLayout $
    equalityRow
      (layoutSDiagram (SThenD SSwap SSwap))
      (layoutSDiagram (SBeside SWire SWire))

--------------------------------------------------------------------------------
-- 6. Tensor interchange: (f⊗g);(h⊗k) = (f;h)⊗(g;k)
--------------------------------------------------------------------------------

tensorInterchangeExample :: ChartOptions
tensorInterchangeExample =
  renderLayout $
    equalityRow lhs rhs
  where
    f = boxF "f"
    g = boxF "g"
    h = boxF "h"
    k = boxF "k"
    lhs =
      layoutSDiagram $
        SThenD
          (SBeside f g)
          (SBeside h k)
    rhs =
      layoutSDiagram $
        SBeside
          (SThenD f h)
          (SThenD g k)

--------------------------------------------------------------------------------
-- 7. Star / Arden: a* = 1 ∨ (a ; a*)
--------------------------------------------------------------------------------

starArdenExample :: ChartOptions
starArdenExample =
  renderLayout $
    equalityRow lhs rhs
  where
    lhs = layoutSDiagram (boxF "a*")
    -- algebraic RHS: join of unit wire and series a ; a*
    rhs =
      Layout
        { picture =
            group
              Nothing
              [ picture unitPath,
                picture seriesPath,
                unnamed
                  [ -- join node
                    GlyphChart
                      ( defaultGlyphStyle
                          & set #glyphShape CircleGlyph
                          & set #size 0.12
                          & set #color accentBlue
                          & set #borderColor accentBlue
                          & set #borderSize 0.02
                          & set #scaleP NoScaleP
                      )
                      [Point 0.15 0],
                    LineChart (wireStyle wireGrey) [[Point 0.15 0, Point 0 0]],
                    LineChart (wireStyle wireGrey) [[Point 1.9 0, Point 2.1 0]]
                  ]
              ],
          leftPorts = [Point 0 0],
          rightPorts = [Point 2.1 0],
          bounds = Rect 0 2.1 (-0.55) 0.55
        }
    unitPath =
      moveLayout (Point 0.15 0.35) $
        Layout
          { picture =
              unnamed
                [ LineChart (wireStyle accentGreen) [[Point 0 0, Point 1.5 0]],
                  TextChart
                    (labelStyle & set #size 0.14 & set #color muteGrey)
                    [("1", Point 0.75 0.18)]
                ],
            leftPorts = [Point 0 0],
            rightPorts = [Point 1.5 0],
            bounds = Rect 0 1.5 (-0.1) 0.25
          }
    seriesPath =
      moveLayout (Point 0.15 (-0.35)) $
        layoutSDiagram (SThenD (boxF "a") (boxF "a*"))

--------------------------------------------------------------------------------
-- 8. Three-strand braid
--------------------------------------------------------------------------------

-- | Braid on three strands: σ1 then σ2.
knotBraid3Example :: ChartOptions
knotBraid3Example =
  renderLayout $
    layoutSDiagram $
      SThenD
        (SBeside SSwap SWire)
        (SBeside SWire SSwap)

--------------------------------------------------------------------------------
-- 9. Closed loop: cap then cup
--------------------------------------------------------------------------------

-- | A single wire that leaves the unit, travels right, and returns to the unit.
-- In the geometric picture this is a circle.
knotCircleExample :: ChartOptions
knotCircleExample =
  renderLayout $
    layoutSDiagram (SThenD SBend' SBend)

--------------------------------------------------------------------------------
-- 10. Trace loop around a box
--------------------------------------------------------------------------------

-- | A feedback loop with a box inside: trace of a one-wire morphism.
knotTraceExample :: ChartOptions
knotTraceExample =
  renderLayout $
    layoutSDiagram $
      SThenD
        SBend'
        (SThenD (SBeside (boxF "f") SWire) SBend)

--------------------------------------------------------------------------------
-- 11. Tangle: swap, cap, cup
--------------------------------------------------------------------------------

-- | A small tangle: two wires cross, one bends back and forth.
knotTangleExample :: ChartOptions
knotTangleExample =
  renderLayout $
    layoutSDiagram $
      SThenD
        (SBeside SSwap SBend')
        (SBeside SBend SSwap)

--------------------------------------------------------------------------------
-- 12. Copy–merge round trip
--------------------------------------------------------------------------------

-- | A copy spider followed by a merge spider: both dots visible, the two
-- fanned wires meeting port-to-port.
copyMergeExample :: ChartOptions
copyMergeExample =
  renderLayout $
    layoutSDiagram (SThenD (SSpider 1 2) (SSpider 2 1))

--------------------------------------------------------------------------------
-- 13. Multi-port boxes
--------------------------------------------------------------------------------

-- | Two-port boxes chained port-to-port, tensored with a plain wire whose
-- stretch clears the box bodies.
multiPortBoxExample :: ChartOptions
multiPortBoxExample =
  renderLayout $
    layoutSDiagram $
      SBeside
        (SThenD (SBox "f" 2 2) (SBox "g" 2 2))
        SWire

--------------------------------------------------------------------------------
-- gallery
--------------------------------------------------------------------------------

-- | Named example SVGs.
allExamples :: [(FilePath, ChartOptions)]
allExamples =
  [ ("yanking-right.svg", yankingRightExample),
    ("yanking-left.svg", yankingLeftExample),
    ("sliding.svg", slidingExample),
    ("trace-sliding.svg", traceSlidingExample),
    ("braid-inverse.svg", braidInverseExample),
    ("tensor-interchange.svg", tensorInterchangeExample),
    ("star-arden.svg", starArdenExample),
    ("knot-braid3.svg", knotBraid3Example),
    ("knot-circle.svg", knotCircleExample),
    ("knot-trace.svg", knotTraceExample),
    ("knot-tangle.svg", knotTangleExample),
    ("copy-merge.svg", copyMergeExample),
    ("multi-port-box.svg", multiPortBoxExample)
  ]

-- | Write every example SVG into the given directory.
writeAllExamples :: FilePath -> IO ()
writeAllExamples dir = do
  createDirectoryIfMissing True dir
  mapM_ (\(fp, co) -> writeChartOptions (dir </> fp) co) allExamples
