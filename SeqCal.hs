module SeqCal where

import Data.List
import Data.Maybe
import Control.Monad

import Data.Set (Set)
import qualified Data.Set as S
-- vi borde kanske ha flera olika filer,
-- def av termer, en for latex osv
-- ska vi investera i en mapp struktur?
{-
   SeqCal -- 
         \ gobby is weird
              --
-}
type Var = Int
type Ctx = Set Formula

type Solve = Maybe

data Formula 
  = Top | Bot
  | Imp Formula Formula
  | Var Var
  | Neg Formula
 deriving (Eq,Ord, Show)

instance Num Formula where
  fromInteger = Var . fromInteger

infixr 2 ~>
(~>) = Imp

data Deduction
  = Intro Ctx Ctx Formula
  | RImp Formula Formula Deduction
  | LImp Formula Formula Deduction Deduction
  | RNeg Formula Deduction
  | LNeg Formula Deduction
  deriving Show

tryStuff :: [Solve a] -> Solve a
tryStuff = listToMaybe . catMaybes

(+:) :: Formula -> Ctx -> Ctx
f +: c = S.insert f c

(-:) :: Formula -> Ctx -> Ctx
f -: c = S.delete f c

(+:+) :: Ctx -> Ctx -> Ctx
(+:+) = S.union

testFormula :: Formula -> Solve Deduction
testFormula f = solve S.empty (S.singleton f)

build :: Deduction -> (Ctx , Ctx)
build ded = case ded of
  Intro g d _ -> (g , d)
  RImp a b x -> let (g,d) = build x
                 in (a -: g , (a ~> b) +: (b -: d))
  LImp a b x1 x2 -> let (g1 , d1) = build x1
                        (g2 , d2) = build x2
                     in ((a ~> b) +: (g1 +:+ (b -: g2))
                         , (a -: d1) +:+ d2)

solve :: Ctx -> Ctx -> Solve Deduction
solve gamma delta | (f : _) <- S.toList is = return $ Intro gamma delta f
  where is = (gamma `S.intersection` delta)
solve gamma delta = tryStuff $ 
     [RImp a b `fmap` solve (a +: gamma) (b +: (i -: delta)) | i@(Imp a b) <- S.toList delta]
  ++ [LImp a b `fmap` solve (i -: gamma) (a +: delta) `ap` solve (b +: (i -: gamma)) delta | i@(Imp a b) <- S.toList gamma]
  
  
scomb = (0 ~> 1 ~> 2) ~> (0 ~> 1) ~> 0 ~> 2
swapF = (0 ~> 1 ~> 2) ~> 1 ~> 0 ~> 2
pierce = ((0 ~> 1) ~> 0) ~> 0
apply = (0 ~> 1) ~> (0 ~> 1)
