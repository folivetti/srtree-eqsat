module Main (main) where

import Data.Char (toLower, toUpper)
import Data.List (intercalate)
import Data.SRTree.EqSat (simplifyEqSat, countParams)
import Options.Applicative
import Text.ParseSR (Output (..), SRAlgs (..))
import Text.ParseSR.IO (withInput, withOutput, withOutputDebug)
import Text.Read (readMaybe)
import Data.SRTree ( SRTree )
import System.IO ( stderr, hPrint )
import Control.Monad ( when )

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
      , stats       :: Bool
      , debug       :: Bool
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
   <*> switch
       ( long "stats"
       <> help "Show the percentage of decrease in the number of parameters. Output into stderr." )
   <*> switch
       ( long "debug"
       <> help "Debug mode: outputs before and after simplification." )

withOutput' :: Bool -> Bool -> String -> Output -> [Either String (SRTree Int Double)] -> IO ()
withOutput' wantStats debugMode fname out trees = do 
    let trees' = fmap (simplifyEqSat <$>) trees
        sts    = zipWith countP trees trees'
        zTrees = zipEither trees trees'
    if debugMode
      then withOutputDebug fname out zTrees
      else withOutput fname out trees'
    when wantStats $ mapM_ (hPrint stderr) sts
    where 
        zipEither [] _ = []
        zipEither _ [] = []
        zipEither (Left x : xs) (_ : ys) = Left x : zipEither xs ys
        zipEither (_ : xs) (Left y : ys) = Left y : zipEither xs ys
        zipEither (Right x : xs) (Right y : ys) = Right (x,y) : zipEither xs ys

        countP :: Either String (SRTree Int Double) -> Either String (SRTree Int Double) -> Either String Double
        countP (Left x) _ = Left x
        countP _ (Left x) = Left x
        countP (Right t1) (Right t2) =
            let c1 = fromIntegral $ countParams t1
                c2 = fromIntegral $ countParams t2
            in  Right $ (c1 - c2) / c1

main :: IO ()
main = do
  args <- execParser opts
  withInput (infile args) (from args) (varnames args) False False
    >>= withOutput' (stats args) (debug args) (outfile args) MATH 
  
  where 
      opts = info (opt <**> helper)
            ( fullDesc <> progDesc "Simplify Symbolic Regression expressions using Equality Saturation."
            <> header "srtree-eqsat - a CLI tool to simplify symbolic regression expressions using equality saturation."
            )
