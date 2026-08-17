{-# LANGUAGE OverloadedLabels #-}

-- | House palette for string-diagram SVGs.
--
-- Colours match @coffee/buff/string-diagram-schematics.html@.
module Strings.Svg.Palette
  ( bgDark,
    boxFill,
    wireGrey,
    accentBlue,
    accentMagenta,
    accentGreen,
    muteGrey,
    wireStyle,
    pathStroke,
    boxStyle,
    labelStyle,
    eqStyle,
  )
where

import Chart
import Optics.Core
import Prelude

-- | Background @#1b1e23@.
bgDark :: Colour
bgDark = Colour (0x1b / 255) (0x1e / 255) (0x23 / 255) 1

-- | Box fill @#21252d@.
boxFill :: Colour
boxFill = Colour (0x21 / 255) (0x25 / 255) (0x2d / 255) 1

-- | Plain wire @#c8ccd4@.
wireGrey :: Colour
wireGrey = Colour (0xc8 / 255) (0xcc / 255) (0xd4 / 255) 1

-- | Primary accent @#4B7FBD@.
accentBlue :: Colour
accentBlue = Colour (0x4b / 255) (0x7f / 255) (0xbd / 255) 1

-- | Secondary accent @#C44E8A@.
accentMagenta :: Colour
accentMagenta = Colour (0xc4 / 255) (0x4e / 255) (0x8a / 255) 1

-- | Result / id accent @#3fa47e@.
accentGreen :: Colour
accentGreen = Colour (0x3f / 255) (0xa4 / 255) (0x7e / 255) 1

-- | Muted labels @#777d87@.
muteGrey :: Colour
muteGrey = Colour (0x77 / 255) (0x7d / 255) (0x87 / 255) 1

-- | Straight wire line style (stroke width in data units).
wireStyle :: Colour -> Style
wireStyle c =
  defaultLineStyle
    & set #color c
    & set #size 0.035
    & set #lineCap (Just LineCapRound)
    & set #scaleP NoScaleP

-- | Stroke-only path style (cups, caps, braid arcs).
pathStroke :: Colour -> Double -> Style
pathStroke c w =
  defaultPathStyle
    & set #color transparent
    & set #borderColor c
    & set #borderSize w
    & set #lineCap (Just LineCapRound)
    & set #lineJoin (Just LineJoinRound)
    & set #scaleP NoScaleP

-- | Filled box with coloured border.
boxStyle :: Colour -> Style
boxStyle stroke =
  defaultRectStyle
    & set #color boxFill
    & set #borderColor stroke
    & set #borderSize 0.025
    & set #scaleP NoScaleP

-- | Label inside a box.
labelStyle :: Style
labelStyle =
  defaultTextStyle
    & set #color wireGrey
    & set #size 0.18
    & set #textAnchor AnchorMiddle
    & set #scaleP NoScaleP

-- | Equals sign between equality sides.
eqStyle :: Style
eqStyle =
  defaultTextStyle
    & set #color muteGrey
    & set #size 0.28
    & set #textAnchor AnchorMiddle
    & set #scaleP NoScaleP
