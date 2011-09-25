{-# LANGUAGE OverloadedStrings , DeriveDataTypeable #-}
module CoreTypes where

import GHC.Exts( IsString(..) )

import Data.Function

import Data.Set (Set)
import qualified Data.Set as S

import Data.Typeable

instance IsString Var where
  fromString = UVar

instance IsString Term where
  fromString = Var . fromString

type Ident = String
data Ctx = Ctx
  { predicates :: Set (Ident, [Term])
  , good :: Set Formula
  , goodSplit :: Set Formula
  , bad :: Set Formula
  }

empty :: Ctx
empty = Ctx
  { predicates = S.empty
  , good = S.empty
  , goodSplit = S.empty
  , bad = S.empty
  }

ctxToSet :: Ctx -> Set Formula
ctxToSet ctx = S.unions
    [ S.map (uncurry Rel) (predicates ctx)
    , good ctx
    , goodSplit ctx
    , bad ctx
    ]

instance Show Ctx where
  show = show . ctxToSet

getPredicates :: Ctx -> Set (Ident, [Term])
getPredicates = predicates

getGood :: Ctx -> Maybe (Formula , Ctx)
getGood ctx | S.null (good ctx) = Nothing
            | otherwise        = Just (x , ctx { good = xs })
  where (x , xs) = S.deleteFindMin (good ctx)

getGoodSplit :: Ctx -> Maybe (Formula , Ctx)
getGoodSplit ctx | S.null (goodSplit ctx) = Nothing
            | otherwise        = Just (x , ctx { goodSplit = xs })
  where (x , xs) = S.deleteFindMin (goodSplit ctx)

getBad :: Ctx -> Set Formula
getBad = bad

infixr 4 +=>
infixr 4 =>+
infixr 4 -:

(+=>) :: Formula -> Ctx -> Ctx
(+=>) = insertLeft

(=>+) :: Formula -> Ctx -> Ctx
(=>+) = insertRight

(-:) :: Formula -> Ctx -> Ctx
(-:) (Rel i ts) ctx = ctx {predicates = S.delete (i,ts) (predicates ctx)}
(-:) form ctx = ctx { good = S.delete form (good ctx)
                      , goodSplit = S.delete form (goodSplit ctx)
                      , bad       = S.delete form (bad ctx)
                      }

(+:+) :: Ctx -> Ctx -> Ctx
c1 +:+ c2 = Ctx
    { predicates = f predicates 
    , good       = f good
    , goodSplit  = f goodSplit
    , bad        = f bad
    }
  where f c = on S.union c c1 c2

insertLeft :: Formula -> Ctx -> Ctx
insertLeft form gamma = case form of
    Top -> inGood
    Bot -> inGood
    Imp _ _ -> inGoodSplit
    Equiv _ _ -> inGoodSplit
    Rel i ts -> gamma { predicates = S.insert (i , ts) (predicates gamma) }
    Neg _ -> inGood
    And _ _ -> inGood
    Or _ _ -> inGoodSplit
    ForAll _ _ -> inBad
    Exists _ _ -> inGood
  where
    inGood = gamma { good = S.insert form (good gamma) }
    inGoodSplit = gamma { goodSplit = S.insert form (goodSplit gamma) }
    inBad  = gamma {bad = S.insert form (bad gamma) }

insertRight :: Formula -> Ctx -> Ctx
insertRight form gamma = case form of
    Top -> inGood
    Bot -> inGood
    Imp _ _ -> inGood
    Equiv _ _ -> inGoodSplit
    Rel i ts -> gamma { predicates = S.insert (i , ts) (predicates gamma) }
    Neg _ -> inGood
    And _ _ -> inGoodSplit
    Or _ _ -> inGood
    ForAll _ _ -> inGood
    Exists _ _ -> inBad
  where
    inGood = gamma { good = S.insert form (good gamma) }
    inGoodSplit = gamma { goodSplit = S.insert form (goodSplit gamma) }
    inBad  = gamma {bad = S.insert form (bad gamma) }


type MVar = Int
data Var
  = GVar Int [MVar]   -- ^ generated 
  | UVar  String  -- ^ from proof
  | MVar MVar  -- ^ meta variable
  deriving (Eq, Ord, Show, Typeable)

data Term
  = Var Var
  | App Ident [Term]
  | Const Ident
  deriving (Eq,Ord,Show, Typeable)

data Formula 
  = Top | Bot
  | Imp Formula Formula
  | Equiv Formula Formula 
    -- ^ A->B /\ B -> A, this is not the = relation (since it takes formulas)
  | Rel Ident [Term]
  | Neg Formula
  | And Formula Formula
  | Or Formula Formula
  | ForAll Var Formula
  | Exists Var Formula
 deriving (Eq,Ord, Show, Typeable)

infixr 2 ~>
(~>) = Imp

(<~>) a b = Equiv a b -- (a ~> b) `And` (b ~> a)

data Deduction
  = Intro Ctx Ctx
  | LBot Ctx Ctx
  | RTop Ctx Ctx
  | RImp Formula Formula Deduction
  | LImp Formula Formula Deduction Deduction
  | REqu Formula Formula Deduction Deduction
  | LEqu Formula Formula Deduction Deduction
  | RNeg Formula Deduction
  | LNeg Formula Deduction
  | RAnd Formula Formula Deduction Deduction
  | ROr Formula Formula Deduction
  | LAnd Formula Formula Deduction
  | LOr Formula Formula Deduction Deduction
  | LForAll Formula Formula Deduction
  | LExists Formula Formula Deduction
  | RForAll Formula Formula Deduction
  | RExists Formula Formula Deduction
  deriving Show
