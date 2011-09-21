module Main where

import Parser
import Latex
import SeqCal



testIt :: FilePath -> String -> IO ()
testIt fp str = case str' `seq` testFormula str' of
   Just ded -> createProofFromDeduction fp ded
   Nothing  -> putStrLn "failed to solve it"
  where str' = parseString str