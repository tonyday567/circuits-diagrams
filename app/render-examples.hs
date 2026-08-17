-- | Write the seven equality SVGs into a directory (default: @other/@).
module Main (main) where

import Strings.Svg.Examples (writeAllExamples)
import System.Environment (getArgs)
import Prelude

main :: IO ()
main = do
  args <- getArgs
  let dir = case args of
        (d : _) -> d
        [] -> "other"
  writeAllExamples dir
  putStrLn ("wrote string-diagram examples to " <> dir <> "/")
