-- | Write the seven equality SVGs into a directory.
module Main (main) where

import Strings.Svg.Examples (writeAllExamples)
import Options.Applicative
import Prelude

data Config = Config
  { cfgDir :: FilePath
  }
  deriving (Show)

configParser :: Parser Config
configParser =
  Config
    <$> option
      str
      ( long "output"
          <> short 'o'
          <> metavar "DIR"
          <> value "other"
          <> showDefault
          <> help "directory to write SVG examples into"
      )

opts :: ParserInfo Config
opts =
  info
    (configParser <**> helper)
    ( fullDesc
        <> progDesc "Write string-diagram SVG examples"
        <> header "render-examples - SVG example generator"
    )

main :: IO ()
main = do
  config <- execParser opts
  writeAllExamples (cfgDir config)
  putStrLn ("wrote string-diagram examples to " <> cfgDir config <> "/")
