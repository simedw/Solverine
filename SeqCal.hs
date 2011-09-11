{-# LANGUAGE OverloadedStrings , PackageImports #-}
module SeqCal where

import GHC.Exts( IsString(..) )

import Debug.Trace
import Data.List
import Data.Maybe
import Control.Monad
import "mtl" Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

instance IsString Var where
  fromString = UVar

instance IsString Term where
  fromString = Var . fromString

type Ident = String
type Ctx = Set Formula

type Solve = MaybeT (State SolveState)

data SolveState = SS
  { nextVar  :: Int
  , nextMeta :: Int
  , metaRestrictions :: Subst
  }


type Subst = Map MVar Term
type MVar = Int
data Var
  = GVar Int     -- ^ generated 
  | UVar  String  -- ^ from proof
  | MVar MVar  -- ^ meta variable
  deriving (Eq, Ord, Show)

data Term
  = Var Var
  | App Ident [Term]
  | Const Ident
  deriving (Eq,Ord,Show)

data Formula 
  = Top | Bot
  | Imp Formula Formula
  | Rel Ident [Term]
  | Neg Formula
  | And Formula Formula
  | Or Formula Formula
  | ForAll Var Formula
  | Exists Var Formula
 deriving (Eq,Ord, Show)

infixr 2 ~>
(~>) = Imp

(<~>) a b = (a ~> b) `And` (b ~> a)

data Deduction
  = Intro Ctx Ctx
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
  | LForAll Formula Formula Deduction
  | LExists Formula Formula Deduction
  | RForAll Formula Formula Deduction
  | RExists Formula Formula Deduction
  deriving Show

getNextVar :: Solve Var
getNextVar = do
  x <- lift $ gets nextVar
  lift $ modify (\s -> s {nextVar = nextVar s + 1})
  return (GVar x)

getNextMVar :: Solve Var
getNextMVar = do 
  x <- lift $ gets nextMeta
  lift $ modify (\s -> s {nextMeta = nextMeta s + 1})
  return (MVar x)

getMetaRestrictions :: Solve Subst
getMetaRestrictions = lift $ gets metaRestrictions

addMetaRestriction :: Subst -> Solve ()
addMetaRestriction sub = lift $ modify (\s -> s {metaRestrictions = fromJust $ sub `composeSub` metaRestrictions s})

tryStuff :: [Solve a] -> Solve a
tryStuff xs = foldl mplus (MaybeT $ return Nothing) xs


(+:) :: Formula -> Ctx -> Ctx
f +: c = S.insert f c

(-:) :: Formula -> Ctx -> Ctx
f -: c = S.delete f c

(+:+) :: Ctx -> Ctx -> Ctx
(+:+) = S.union

agree :: Subst -> Subst -> Bool
agree sub1 sub2 = all (\x -> M.lookup x sub1 == M.lookup x sub2)
                      (M.keys sub1 `intersect` M.keys sub2)

idSub = M.empty
composeSub :: Subst -> Subst -> Maybe Subst
composeSub sub1 sub2 | agree sub1 sub2 = Just $ M.union (M.map (applySubst sub2) sub1) sub2
                     | otherwise = Nothing

applySubst :: Subst -> Term -> Term
applySubst sub term = case term of
  Const _ -> term
  Var (MVar x) -> case M.lookup x sub of
    Nothing -> term
    Just y  -> y
  Var _ -> term
  App f ts -> App f (map (applySubst sub) ts)

unifyTerms :: [Term] -> [Term] -> Maybe Subst
unifyTerms [] [] = Just idSub
unifyTerms (t : ts) (s : ss) = do
  sub1 <- unify t s
  sub2 <- unifyTerms (map (applySubst sub1) ts) (map (applySubst sub1) ss)
  (sub1 `composeSub` sub2)
unifyTerms _ _ = Nothing

unify :: Term -> Term -> Maybe Subst
unify (Var (MVar x)) t | not (x `occur` t) = Just $ M.singleton x t
unify t (Var (MVar x)) | not (x `occur` t) = Just $ M.singleton x t
unify (Var x) (Var y) | x == y = Just idSub
unify (App f ts) (App f' ss) | f == f' = unifyTerms ts ss
unify (Const c) (Const d) | c == d = Just idSub
unify _ _ = Nothing

occur :: MVar -> Term -> Bool
occur x (Var (MVar y)) = x == y
occur x (Var _) = False
occur x (App _ ts) = any (occur x) ts
occur x (Const _) = False

testFormula :: Formula -> Maybe Deduction
testFormula f = evalState (runMaybeT (solve S.empty (S.singleton f)))
  $ SS { nextVar = 0, nextMeta = 0, metaRestrictions = M.empty}

build :: Deduction -> (Ctx , Ctx)
build ded = case ded of
  Intro g d -> (g , d)
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
  RForAll i o x -> let (g,d) = build x
                   in (g, i +: (o -: d))
  LForAll i o x -> let (g,d) = build x
                   in (i +: (o -: g),d)
  RExists i o x -> let (g,d) = build x
                   in (g, i +: (o -: d))
  LExists i o x -> let (g,d) = build x
                   in (i +: (o -: g),d)

substTerm :: Var -> Var -> Term -> Term
substTerm x y t = case t of
    Var v | x == v -> Var y
          | otherwise -> t
    App i terms -> App i (map (substTerm x y) terms)
    Const _ -> t

-- Första byts ut mot andra
subst :: Var -> Var -> Formula -> Formula
subst x y form = case form of
    Rel f ts -> Rel f (map (substTerm x y) ts)
    Top -> Top
    Bot -> Bot
    Imp a b -> Imp (rec a) (rec b)
    Neg a -> Neg (rec a)
    And a b -> And (rec a) (rec b)
    Or a b -> Or (rec a) (rec b)
    ForAll x' a | x == x' -> form
                | otherwise -> ForAll x' (rec a)
    Exists x' a | x == x' -> form
                | otherwise -> Exists x' (rec a)
  where
    rec = subst x y

solve :: Ctx -> Ctx -> Solve Deduction
solve gamma delta = case () of
    _ | (f : _) <- S.toList is -> return $ Intro gamma delta
    _ -> do
      subst <- getMetaRestrictions
      let possible =  [ (id1 , sub) 
                | Rel id1 t1 <- S.toList gamma
                , Rel id2 t2 <- S.toList delta
                , id1 == id2
                , Just sub <- [unifyTerms t1 t2]
                ]
      let p' = filter fst $ map (\(_,s) -> (agree s subst,s)) possible
      if not (null p')
         then do
            addMetaRestriction (snd . head $ p')
            return $ Intro gamma delta
         else solve' gamma delta 
  where
    is = (gamma `S.intersection` delta)
    solve' gamma delta | Top `S.member` delta = return $ RTop gamma delta
    solve' gamma delta | Bot `S.member` gamma = return $ LBot gamma delta
    solve' gamma delta = tryStuff $ 
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
     ++ [ LImp a b `fmap` solve (i -: gamma) (a +: delta) `ap` solve (b +: (i -: gamma))  delta | i@(Imp a b) <- S.toList gamma]
     ++ [ do v' <- getNextVar
             let o = subst v v' f
             p  <- solve gamma (o +: (i -: delta))
             return $ RForAll i o p | i@(ForAll v f) <- S.toList delta]
     ++ [ do v' <- getNextVar
             let o = subst v v' f
             p <- solve (o +: (i -: gamma)) delta
             return $ LExists i o p | i@(Exists v f) <- S.toList gamma]
     ++ [ do v' <- getNextMVar
             let o = subst v v' f
             p <- solve (o +: (gamma)) delta
             v'' <- getNextMVar
             return $ LForAll i o p | i@(ForAll v f) <- S.toList gamma]
     ++ [ do v' <- getNextMVar
             let o = subst v v' f
             p  <- solve gamma (o +: (delta))
             return $ RExists i o p | i@(Exists v f) <- S.toList delta]

dblNeg = Neg (Neg (Rel "P" [])) ~> Rel "P" []
scomb = let (p, q, r) = (Rel "P" [],Rel "Q" [], Rel "R" [])
  in (p ~> q ~> r) ~> (p ~> q) ~> p ~> r
swapF = let (p, q, r) = (Rel "P" [], Rel "Q" [], Rel "R" [])
  in (p ~>q ~> r) ~> q ~> p ~> r

natti = ((Rel "N" [Const "0"]) `And` (ForAll "x" $ (Rel "N" ["x"]) ~> Rel "N" [App "S" ["x"]])) ~> Rel "N" [App "S" [App "S" [Const "0"]]]

