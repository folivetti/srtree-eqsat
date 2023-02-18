{-# language LambdaCase #-}
module Main (main) where

import Data.SRTree.FixTree
import Options.Applicative
import Data.Bifunctor ( first )
import Data.Char ( toLower, toUpper )
import Text.Read ( readMaybe )
import Data.List ( intercalate )
import Text.ParseSR ( SRAlgs(..), Output(..) )
import Text.ParseSR.IO ( withInput, withOutput )
import qualified Data.ByteString.Char8 as B
import Data.SRTree
import qualified Data.SRTree.Print as P
import System.IO 
import Control.Monad

envelope :: a -> [a] -> [a]
envelope c xs = c : xs <> [c]

sralgsHelp :: [String]
sralgsHelp = map (envelope '\'' . map toLower . show) [toEnum 0 :: SRAlgs ..]

sralgsReader :: ReadM SRAlgs
sralgsReader = do
  sr <- map toUpper <$> str
  eitherReader $ case readMaybe sr of
    Nothing -> pure . Left $ "unknown algorithm. Available options are " <> intercalate "," sralgsHelp
    Just x  -> pure . Right $ x

data Args = Args
    {   from        :: SRAlgs
      , infile      :: String
      , outfile     :: String
      , varnames    :: String
    } deriving Show

opt :: Parser Args
opt = Args
   <$> option sralgsReader
       ( long "from"
       <> short 'f'
       <> metavar ("[" <> intercalate "|" sralgsHelp <> "]")
       <> help "Input expression format" )
   <*> strOption
       ( long "input"
       <> short 'i'
       <> metavar "INPUT"
       <> showDefault
       <> value ""
       <> help "Input file containing expressions. Empty string gets expression from stdin." )
   <*> strOption
       ( long "output"
       <> short 'o'
       <> metavar "OUTPUT"
       <> showDefault
       <> value ""
       <> help "Output file to store expressions. Empty string prints expressions to stdout." )
   <*> strOption
       ( long "varnames"
       <> short 'v'
       <> metavar "VARNAMES"
       <> showDefault
       <> value ""
       <> help "Comma separated list of variables names. Empty list assumes the default of each algorithm (e.g, \"x,y,epsilon\")." )

main :: IO ()
main = do
  args <- execParser opts
  withInput (infile args) (from args) (varnames args) False
    >>= withOutput (outfile args) MATH . fmap (simplifyEqSat <$>)
  
  where 
      opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Simplify Symbolic Regression expressions using Equality Saturation."
            <> header "srtree-eqsat - a CLI tool to simplify symbolic regression expressions using equality saturation."
            )
