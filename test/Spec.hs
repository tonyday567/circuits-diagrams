-- | Structural oracles for string-diagram layout.
module Main (main) where

import Circuit.Poly.StringDiagram
  ( SDiagram (..),
    beside,
    boxLabelled,
    sCopy,
    sCreate,
    sDelete,
    sMerge,
    skeleton,
    thenD,
    wire,
  )
import Chart (Point (..))
import Circuit.Poly (lens)
import Strings.Svg.Layout
import System.Exit (exitFailure)
import Prelude

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

approx :: Double -> Double -> Bool
approx a b = abs (a - b) < 0.08

ptApprox :: Point Double -> Point Double -> Bool
ptApprox (Point x1 y1) (Point x2 y2) = approx x1 x2 && approx y1 y2

ptsApprox :: [Point Double] -> [Point Double] -> Bool
ptsApprox ps qs = length ps == length qs && and (zipWith ptApprox ps qs)

main :: IO ()
main = do
  putStrLn "strings-svg structural oracles"

  let w = layoutSDiagram (skeleton wire)
  assert "skeleton wire is one line" $ countLines w == 1 && countRects w == 0

  let b = layoutSDiagram (skeleton (boxLabelled "f" (lens id (\_ da -> da))))
  assert "skeleton box is one rect + two line segments" $
    countRects b == 1 && countLines b == 2

  let d1 = layoutSDiagram SWire
      d2 = layoutSDiagram SWire
      ten = layoutSDiagram (SBeside SWire SWire)
      seq' = layoutSDiagram (SThenD SWire SWire)
  assert "beside height ≈ h1 + gap + h2" $
    approx (layoutHeight ten) (layoutHeight d1 + tensorGap + layoutHeight d2)
  assert "thenD width ≈ w1 + gap + w2" $
    approx (layoutWidth seq') (layoutWidth d1 + composeGap + layoutWidth d2)

  let cup = layoutSDiagram SBend
      cap = layoutSDiagram SBend'
  assert "bend (cup) is one path" $ countPaths cup == 1
  assert "bend' (cap) is one path" $ countPaths cap == 1

  let sw = layoutSDiagram SSwap
  assert "swap has crossing line segments (≥2)" $ countLines sw >= 2

  let typedBeside = layoutSDiagram (skeleton (beside wire wire))
      typedThen = layoutSDiagram (skeleton (thenD wire wire))
  assert "typed beside skeleton layouts" $ layoutHeight typedBeside > layoutHeight d1
  assert "typed thenD skeleton layouts" $ layoutWidth typedThen > layoutWidth d1

  -- L2c: multi-port boxes
  let box2 = layoutSDiagram (SBox "f" 2 2)
      chain2 = layoutSDiagram (SThenD (SBox "f" 2 2) (SBox "g" 2 2))
  assert "two-port box has two ports each side" $
    length (leftPorts box2) == 2 && length (rightPorts box2) == 2
  assert "two-port box grows taller than one-port box" $
    layoutHeight box2 > layoutHeight b
  assert "two-port box chain aligns both port pairs (pinned)" $
    ptsApprox (leftPorts chain2) [Point 0 0.25, Point 0 (-0.25)]
      && ptsApprox (rightPorts chain2) [Point 2.12 0.25, Point 2.12 (-0.25)]

  -- L2c: port-count mismatch in thenL is a visible truncation
  let mismatch = layoutSDiagram (SThenD SWire (SBeside SWire SWire))
  assert "port-count mismatch truncates with a dangling marker" $
    countGlyphs mismatch == 1 && length (rightPorts mismatch) == 2

  -- L2c: beside stretches wires without crossings
  let tall = layoutSDiagram (SBeside (SBox "f" 2 2) SWire)
      ys = [y | Point _ y <- leftPorts tall]
  assert "beside mismatched heights keeps ports strictly ordered" $
    and (zipWith (>) ys (drop 1 ys))
  case (ys, leftPorts box2) of
    (yTop : _, Point _ boxTop0 : _) ->
      -- standalone box bounds are symmetric about y=0, so the moved box
      -- bottom is its vertical shift minus half its height
      let boxBot = yTop - boxTop0 - layoutHeight box2 / 2
       in assert "stretched wire clears the box body" $
            and [y + 0.05 < boxBot | y <- drop (length (leftPorts box2)) ys]
    _ -> assert "stretched wire clears the box body" False

  -- L2c: spiders
  let cp = layoutSDiagram sCopy
      mg = layoutSDiagram sMerge
      roundTrip = layoutSDiagram (SThenD sCopy sMerge)
  assert "copy spider fans out to two outputs (pinned)" $
    ptsApprox (rightPorts cp) [Point 1 0.25, Point 1 (-0.25)]
  assert "copy outputs meet merge inputs exactly" $
    ptsApprox ((\(Point _ y) -> Point 0 y) <$> rightPorts cp) (leftPorts mg)
  assert "copy-merge round trip shows both dots" $ countGlyphs roundTrip == 2
  assert "round-trip spider legs are curved paths" $ countPaths roundTrip == 6
  assert "round trip ends on a single centred wire (pinned)" $
    ptsApprox (rightPorts roundTrip) [Point 2.12 0]

  let del = layoutSDiagram sDelete
      cre = layoutSDiagram sCreate
  assert "delete terminates its input with a dot" $
    rightPorts del == [] && countGlyphs del == 1 && countPaths del == 1
  assert "create opens a dot into an output" $
    leftPorts cre == [] && countGlyphs cre == 1 && countPaths cre == 1

  putStrLn "all structural oracles passed"
