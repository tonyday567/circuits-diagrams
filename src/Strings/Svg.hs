-- | String-diagram SVG rendering for @string-diagrams@ via @chart-svg@.
--
-- Pipeline:
--
-- 1. Build a typed 'Circuit.Poly.StringDiagram.Diagram' (or an untyped 'SDiagram').
-- 2. Forget types with 'skeleton' (if needed).
-- 3. 'layoutSDiagram' → 'Layout' (ports + bounds + 'ChartTree').
-- 4. 'renderLayout' / 'renderSDiagram' → 'ChartOptions'.
-- 5. 'writeChartOptions' → SVG file.
module Strings.Svg
  ( -- * Re-exports from string-diagrams
    module Circuit.Poly.StringDiagram,

    -- * Layout
    Layout (..),
    layoutSDiagram,
    layoutWidth,
    layoutHeight,
    countCharts,
    countLines,
    countRects,
    countPaths,

    -- * Render
    renderLayout,
    renderSDiagram,
    renderDiagram,
    equalityRow,
    withBackground,

    -- * Palette
    module Strings.Svg.Palette,

    -- * Examples
    module Strings.Svg.Examples,
  )
where

import Circuit.Poly.StringDiagram
import Strings.Svg.Examples
import Strings.Svg.Layout
import Strings.Svg.Palette
import Strings.Svg.Render
