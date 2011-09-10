module SeqCal where

import Data.List
import Data.Maybe
import Control.Monad

import Data.Set (Set)
import qualified Data.Set as S
type Var = Int
type Ctx = Set Formula

type Solve = Maybe

data Formula 
  = Top | Bot
  | Imp Formula Formula
  | Var Var
  | Neg Formula
  | And Formula Formula
  | Or Formula Formula
 deriving (Eq,Ord, Show)

instance Num Formula where
  fromInteger = Var . fromInteger

infixr 2 ~>
(~>) = Imp

(<~>) a b = (a ~> b) `And` (b ~> a)

data Deduction
  = Intro Ctx Ctx Formula
  | LBot Ctx Ctx
  | RTop Ctx Ctx
  | RImp Formula Formula Deduction
  | LImp Formula Formula Deduction Deduction
  | RNeg Formula Deduction
  | LNeg Formula Deduction
  | RAnd Formula Formula Deduction Deduction
  | ROr Formula Formula Deduction
  | LAnd Formula Formula Deduction
  | LOr Formula Formula Deduction Deduction
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
  LBot g d -> (g , d)
  RTop g d -> (g , d)
  RImp a b x -> let (g,d) = build x
                 in (a -: g , (a ~> b) +: (b -: d))
  LImp a b x1 x2 -> let (g1 , d1) = build x1
                        (g2 , d2) = build x2
                     in ((a ~> b) +: (g1 +:+ (b -: g2))
                         , (a -: d1) +:+ d2)
  RNeg a x -> let (g , d) = build x
               in (a -: g, (Neg a) +: d)
  LNeg a x -> let (g , d) = build x
               in ((Neg a) +: g, a -: d)
  RAnd a b x1 x2 -> let (g1, d1) = build x1
                        (g2, d2) = build x2
                     in (g1 +:+ g2
                        ,(And a b) +: (a -: d1) +:+ (b -: d2))
  ROr a b x      -> let (g, d) = build x
                     in (g, (Or a b) +: (b -: (a -: d)))
  LAnd a b x     -> let (g, d) = build x
                     in ((And a b) +: (a -: (b -: g)), d)
  LOr a b x1 x2  -> let (g1, d1) = build x1
                        (g2, d2) = build x2
                     in ((Or a b) +: (a -: g1) +:+ (b -: g2)
                        ,d1 +:+ d2)


solve :: Ctx -> Ctx -> Solve Deduction
solve gamma delta | (f : _) <- S.toList is = return $ Intro gamma delta f
  where is = (gamma `S.intersection` delta)
solve gamma delta | Top `S.member` delta = return $ RTop gamma delta
solve gamma delta | Bot `S.member` gamma = return $ LBot gamma delta
solve gamma delta = tryStuff $ 
     [ RImp a b `fmap` solve (a +: gamma) (b +: (i -: delta)) | i@(Imp a b) <- S.toList delta]
  ++ [ RNeg a `fmap` solve (a +: gamma) (i -: delta) | i@(Neg a) <- S.toList delta]
  ++ [ LNeg a `fmap` solve (i -: gamma) (a +: delta) | i@(Neg a) <- S.toList gamma]
  ++ [ LAnd a b `fmap` solve (a +: (b +: (i -: gamma))) delta | i@(And a b) <- S.toList gamma]
  ++ [ ROr a b `fmap` solve gamma (a +: (b +: (i -: delta))) | i@(Or a b) <- S.toList delta]
  ++ [ RAnd a b `fmap` solve gamma (a +: (i -: delta))
                `ap`   solve gamma (b +: (i -: delta))
     | i@(And a b ) <- S.toList delta]
  ++ [ LOr a b `fmap`  solve (a +: (i -: gamma)) delta
                `ap`   solve (b +: (i -: gamma)) delta
     | i@(Or a b ) <- S.toList gamma]
  ++ [ LImp a b `fmap` solve (i -: gamma) (a +: delta) `ap` solve (b +: (i -: gamma)) delta | i@(Imp a b) <- S.toList gamma]
  
dblNeg = (Neg (Neg 0)) ~> 0  
scomb = (0 ~> 1 ~> 2) ~> (0 ~> 1) ~> 0 ~> 2
swapF = (0 ~> 1 ~> 2) ~> 1 ~> 0 ~> 2
pierce = ((0 ~> 1) ~> 0) ~> 0
apply = (0 ~> 1) ~> (0 ~> 1)
