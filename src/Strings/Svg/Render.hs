{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render a laid-out string diagram as 'ChartOptions' (SVG via chart-svg).
module Strings.Svg.Render
  ( renderLayout,
    renderSDiagram,
    renderDiagram,
    equalityRow,
    withBackground,
    padLayout,
  )
where

import Chart
import Circuit.Poly.StringDiagram (Diagram, SDiagram, skeleton)
import Data.ByteString (ByteString)
import Optics.Core
import Strings.Svg.Layout
import Strings.Svg.Palette
import Prelude

-- | Pad a layout's bounds (for background / viewBox breathing room).
padLayout :: Double -> Layout -> Layout
padLayout p lay =
  lay {bounds = expandBounds p (bounds lay)}
  where
    expandBounds d (Rect x z y w) = Rect (x - d) (z + d) (y - d) (w + d)

-- | Dark background rect behind a chart tree, spanning the given bounds.
withBackground :: Rect Double -> ChartTree -> ChartTree
withBackground r tree =
  group
    Nothing
    [ unnamed [RectChart (blob bgDark & set #scaleP NoScaleP) [r]],
      tree
    ]

-- | Render a 'Layout' to chart options (no hud).
renderLayout :: Layout -> ChartOptions
renderLayout lay =
  mempty
    & set #hudOptions mempty
    & set #chartTree (withBackground b (picture lay))
    & set
      (#markupOptions % #chartAspect)
      UnscaledAspect
    & set
      (#markupOptions % #cssOptions % #fontFamilies)
      monoFont
    & set
      (#markupOptions % #cssOptions % #preferColorScheme)
      PreferNormal
    & set
      (#markupOptions % #cssOptions % #cssExtra)
      ("svg { background-color: " <> showRGB bgDark <> "; }\n")
    & set (#markupOptions % #markupHeight) (Just h)
  where
    lay' = padLayout 0.15 lay
    b = bounds lay'
    Rect _ _ y w = b
    -- keep height readable; width follows UnscaledAspect from data
    h = max 120 (min 360 (180 * (w - y + 0.01)))
    monoFont :: ByteString
    monoFont = "svg { font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace; }\n"

-- | Layout then render an untyped skeleton.
renderSDiagram :: SDiagram -> ChartOptions
renderSDiagram = renderLayout . layoutSDiagram

-- | Forget types via 'skeleton', then render.
renderDiagram :: Diagram a da b db -> ChartOptions
renderDiagram = renderSDiagram . skeleton

-- | Place two layouts side by side with an equals sign between them.
equalityRow :: Layout -> Layout -> Layout
equalityRow left right =
  Layout
    { picture = group Nothing [picture l', eqTree, picture r'],
      leftPorts = leftPorts l',
      rightPorts = rightPorts r',
      bounds = bounds l' <> bounds r' <> eqBounds
    }
  where
    gap = 0.45
    l' = moveLayout (Point (-lx left) (-midY left)) left
    eqX = rx l' + gap
    r' = moveLayout (Point (eqX + gap - lx right) (-midY right)) right
    eqTree = unnamed [TextChart eqStyle [("=", Point eqX 0)]]
    eqBounds = Rect (eqX - 0.2) (eqX + 0.2) (-0.2) 0.2
    lx (Layout _ _ _ (Rect x _ _ _)) = x
    rx (Layout _ _ _ (Rect _ z _ _)) = z
    midY (Layout _ _ _ (Rect _ _ y w)) = (y + w) / 2
