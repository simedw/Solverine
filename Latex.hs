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
conj      = comm0_ "wedge"
disj      = comm0_ "vee"
top       = comm0_ "top"
bot       = comm0_ "bot"


lintercalate :: Monad m => LaTeX m -> [LaTeX m] -> LaTeX m
lintercalate t (a:a':as) = a >> t >> lintercalate t (a':as)
lintercalate _ [a]       = a
lintercalate _ _         = ""

lpretty :: Monad m => Formula -> LaTeX m
lpretty = pretty' 0
  where
    vars = [1..] >>= flip replicateM ['a'..'z']
    pretty' :: Monad m => Int -> Formula -> LaTeX m
    pretty' i f = case f of
        Imp a b -> paren i 2 $ do 
            pretty' 3 a
            math $ imp
            pretty' 1 b
        Neg a -> paren i 3 $ do
          math $ neg
          pretty' 2 a
        Var v   -> fromString $ vars !! v
        Top -> math top
        Bot -> math bot
        Or a b -> paren i 1 $ do
            pretty' 2 a
            math $ disj
            pretty' 2 b
        And a b -> paren i 1 $ do
            pretty' 2 a
            math $ conj
            pretty' 2 b

    paren x y m | x >= y = do
      "("
      m
      ")"
                | otherwise = m

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
            unary $ gamma |- delta 
        LBot gamma delta -> do
            axiom ""
            rlabel (fromString "L" >> math bot)
            unary $ gamma |- delta 
        RTop gamma delta -> do
            axiom ""
            rlabel (fromString "R" >> math top)
            unary $ gamma |- delta 
        RImp f1 f2 prf -> do
            tree' prf 
            rlabel (fromString "R" >> math imp)
            unary (g |- d)
        LImp f1 f2 prf1 prf2 -> do
            tree' prf1
            tree' prf2
            rlabel (fromString "L" >> math imp)
            binary (g |- d)
        RNeg f prf -> do
            tree' prf
            rlabel (fromString "R" >> math neg)
            unary (g |- d)
        LNeg f prf -> do
            tree' prf
            rlabel (fromString "L" >> math neg)
            unary (g |- d)
        RAnd f1 f2 prf1 prf2 -> do
            tree' prf1
            tree' prf2
            rlabel (fromString "R" >> math conj)
            binary (g |- d)
        LAnd f1 f2 prf -> do
            tree' prf
            rlabel (fromString "L" >> math conj)
            unary (g |- d)
        ROr f1 f2 prf -> do
            tree' prf
            rlabel (fromString "R" >> math disj)
            unary (g |- d)
        LOr f1 f2 prf1 prf2 -> do
            tree' prf1
            tree' prf2
            rlabel (fromString "L" >> math disj)
            binary (g |- d)
      where
        (g,d) = build ded
proof :: Monad m => Deduction -> LaTeX m
proof dd = do
    documentclass [] article
    usepackage [] "bussproofs"
    author "Solverine"
    title "Proof"
    date ""
    document $ do 
       -- maketitle
        buildTree dd

createProof :: FilePath -> Formula -> IO ()
createProof filePath ff = case testFormula ff of
    Just dd -> createProofFromDeduction filePath dd
    Nothing -> putStrLn "Sorry"
createProofFromDeduction :: FilePath -> Deduction -> IO ()
createProofFromDeduction filePath dd = 
    writeFile filePath . unlines $ render (proof dd)
