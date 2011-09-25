{-# LANGUAGE OverloadedStrings, NoMonomorphismRestriction #-}
module Latex where

import CoreTypes
import SeqCal


import System.Timeout
import Control.Monad
import Data.Char
import Data.Set (Set)
import qualified Data.Set as S
import Text.LaTeX hiding ((|-),proof)


proofTree = env    "prooftree"
axiom     = comm1  "AxiomC"
unary     = comm1  "UnaryInfC"
binary    = comm1  "BinaryInfC"
rlabel    = comm1  "RightLabel"
imp       = comm0_ "rightarrow"
equiv     = comm0_ "leftrightarrow"
neg       = comm0_ "neg"
turnstile = math $ comm0_ "vdash"
conj      = comm0_ "wedge"
disj      = comm0_ "vee"
top       = comm0_ "top"
bot       = comm0_ "bot"
forAll    = comm0_ "forall"
exists    = comm0_ "exists"


lintercalate :: Monad m => LaTeX m -> [LaTeX m] -> LaTeX m
lintercalate t (a:a':as) = a >> t >> lintercalate t (a':as)
lintercalate _ [a]       = a
lintercalate _ _         = ""

prettyV :: Monad m => Var -> LaTeX m
prettyV t = case t of
    UVar v -> fromString v
    GVar i xs -> math $ do
          fromString $ '\'' : vars !! i
          "_{"
          lintercalate "," $ map (prettyV . MVar) xs 
          "}"
    MVar v  -> fromString $ meta !! v
  where
   vars = [1..] >>= flip replicateM ['a'..'z']
   meta = map (('?' :) . map toUpper) vars

prettyT :: Monad m => Term -> LaTeX m
prettyT t = case t of
    Var x -> prettyV x
    Const c -> fromString c
    App idnt terms -> do
          fromString idnt
          "(" 
          lintercalate "," (map prettyT terms)
          ")"

lpretty :: Monad m => Formula -> LaTeX m
lpretty = pretty' 0
  where
    pretty' :: Monad m => Int -> Formula -> LaTeX m
    pretty' i f = case f of
        Imp a b -> paren i 2 $ do 
            pretty' 3 a
            math $ imp
            pretty' 1 b
        Equiv a b -> paren i 2 $ do 
            pretty' 3 a
            math $ equiv
            pretty' 3 b
        Neg a -> paren i 3 $ do
          math $ neg
          pretty' 2 a
        Rel idnt terms | null terms -> fromString idnt 
                       | otherwise  -> do
          fromString idnt
          "(" 
          lintercalate "," (map prettyT terms)
          ")"
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
        ForAll a b -> do
            math $ forAll
            prettyV a
            "."
            pretty' 2 b
        Exists a b -> do
            math $ exists
            prettyV a
            "."
            pretty' 2 b

    paren x y m | x >= y = do
      "("
      m
      ")"
                | otherwise = m

(|-) :: Monad m => Ctx -> Ctx -> LaTeX m
(|-) gamma delta = do
    lintercalate "," $ [ lpretty x | x <- S.toList $ ctxToSet gamma]
    turnstile
    lintercalate "," $ [ lpretty x | x <- S.toList $ ctxToSet delta]



buildTree :: Monad m => Deduction -> LaTeX m
buildTree = proofTree . tree'
  where 
    tree' ded = case ded of
        Intro gamma delta  -> zero "Intro"
        LBot gamma delta -> zero $ "L" >> math bot
        RTop gamma delta -> zero $ "R" >> math top
        RImp f1 f2 prf -> one prf $ "R" >> math imp
        LImp f1 f2 prf1 prf2 -> two prf1 prf2 $ "L" >> math imp
        REqu f1 f2 prf1 prf2 -> two prf1 prf2 $ "R" >> math equiv
        LEqu f1 f2 prf1 prf2 -> two prf1 prf2 $ "L" >> math equiv
        RNeg f prf -> one prf $ "R" >> math neg
        LNeg f prf -> one prf $ "L" >> math neg
        RAnd f1 f2 prf1 prf2 -> two prf1 prf2 $ "R" >> math conj
        LAnd f1 f2 prf -> one prf $ "L" >> math conj
        ROr f1 f2 prf -> one prf $ "R" >> math disj
        LOr f1 f2 prf1 prf2 -> two prf1 prf2 $ "L" >> math disj
        RForAll f _ prf -> one prf $ "R" >> math forAll
        LForAll f _ prf -> one prf $ "L" >> math forAll
        RExists f _ prf -> one prf $ "R" >> math exists
        LExists f _ prf -> one prf $ "L" >> math exists
      where
        zero lab = do
          axiom ""
          rlabel lab
          unary (g |- d)
        one prf lab = do
          tree' prf
          rlabel lab
          unary (g |- d)
        two prf1 prf2 lab = do
          tree' prf1
          tree' prf2
          rlabel lab
          binary (g |- d)
        (g,d) = build ded
proof :: Monad m => Deduction -> LaTeX m
proof dd = do
    documentclass [] article
    usepackage [] "bussproofs"
    usepackage [] "rotating"
    usepackage [] "fullpage"
    usepackage ["paperwidth=20in"] "geometry"
    author "Solverine"
    title "Proof"
    date ""
--    comm0_ "setlength{\\textwidth}{520pt}"
--    comm0_ "special{papersize=2100mm,2970mm}"
    document $ do 
       -- maketitle
        {-comm1 "tiny" $ -} {-env "sidewaysfigure" $-} buildTree dd

createProof :: FilePath -> Formula -> IO ()
createProof filePath ff = do
    res <- timeout 100000 $ case testFormula ff of 
        Just dd -> createProofFromDeduction filePath dd >> return True
        Nothing -> return False
    case res of
        Just True -> putStrLn "proved ψ(｀∇´)ψ"
        Just False -> putStrLn "couldn't prove (><)"
        Nothing -> putStrLn "timeout T_T"

createProofFromDeduction :: FilePath -> Deduction -> IO ()
createProofFromDeduction filePath dd = 
    writeFile filePath . unlines $ render (proof dd)
