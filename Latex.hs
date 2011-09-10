{-# LANGUAGE OverloadedStrings, NoMonomorphismRestriction #-}
module Latex where

import SeqCal

import Control.Monad
import Data.Set (Set)
import qualified Data.Set as S
import Text.LaTeX hiding ((|-),proof)


proofTree = env    "prooftree"
axiom     = comm1  "AxiomC"
unary     = comm1  "UnaryInfC"
binary    = comm1  "BinaryInfC"
rlabel    = comm1  "RightLabel"
imp       = comm0_ "rightarrow"
neg       = comm0_ "neg"
turnstile = math $ comm0_ "vdash"

lintercalate :: Monad m => LaTeX m -> [LaTeX m] -> LaTeX m
lintercalate t (a:a':as) = a >> t >> lintercalate t (a':as)
lintercalate _ [a]       = a
lintercalate _ _         = ""

lpretty :: Monad m => Formula -> LaTeX m
lpretty = pretty' 
  where
    vars = [1..] >>= flip replicateM ['a'..'z']
    pretty' :: Monad m => Formula -> LaTeX m
    pretty' f = case f of
        Imp a b -> do 
            "("
            pretty' a
            math $ imp
            pretty' b
            ")"
        Neg a -> do
          "(" -- par
          math $ neg
          pretty' a
          ")" -- par
        Var v   -> fromString $ vars !! v

(|-) :: Monad m => Ctx -> Ctx -> LaTeX m
(|-) gamma delta = do
    lintercalate "," $ [ lpretty x | x <- S.toList gamma]
    turnstile
    lintercalate "," $ [ lpretty x | x <- S.toList delta]



buildTree :: Monad m => Deduction -> LaTeX m
buildTree = proofTree . tree'
  where 
    tree' ded = case ded of
        Intro gamma delta f -> do
            axiom ""
            rlabel (fromString "Intro")
            unary $ gamma |- delta -- (f `S.insert` gamma) |- (f `S.insert` delta)
        RImp f1 f2 prf -> do
            tree' prf 
            rlabel (fromString "R" >> math imp)
            unary (g |- d)
        LImp f1 f2 prf1 prf2 -> do
            tree' prf1
            tree' prf2
            rlabel (fromString "L" >> math imp)
            binary (g |- d)
      where
        (g,d) = build ded
proof :: Monad m => Deduction -> LaTeX m
proof dd = do
    documentclass [] article
    usepackage [] "bussproofs"
    title "Proof"
    document $ do 
        maketitle
        buildTree dd

createProof :: FilePath -> Formula -> IO ()
createProof filePath ff = case testFormula ff of
    Just dd -> createProofFromDeduction filePath dd
    Nothing -> putStrLn "Sorry"
createProofFromDeduction :: FilePath -> Deduction -> IO ()
createProofFromDeduction filePath dd = 
    writeFile filePath . unlines $ render (proof dd)
