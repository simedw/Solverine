{-# LANGUAGE OverloadedStrings , PackageImports, DeriveDataTypeable #-}
module SeqCal where


import Debug.Trace
import Data.Function
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

import System.Random
import System.Random.Shuffle -- cabal install random-shuffle

import CoreTypes

type Solve = MaybeT (State SolveState)

data SolveState = SS
  { nextVar  :: Int
  , nextMeta :: Int
  , metaRestrictions :: Subst
  , stdgen :: StdGen
  }


type Subst = Map MVar Term



getNextVar :: [MVar] -> Solve Var
getNextVar xs = do
  x <- lift $ gets nextVar
  lift $ modify (\s -> s {nextVar = nextVar s + 1})
  return (GVar x xs )

getNextMVar :: Solve Var
getNextMVar = do 
  x <- lift $ gets nextMeta
  lift $ modify (\s -> s {nextMeta = nextMeta s + 1})
  return (MVar x)

getMetaRestrictions :: Solve Subst
getMetaRestrictions = lift $ gets metaRestrictions

addMetaRestriction :: Subst -> Solve ()
addMetaRestriction sub = lift $ modify (\s -> s {metaRestrictions = fromJust $ sub `composeSub` metaRestrictions s})

getTheStdGen :: Solve StdGen
getTheStdGen = do
  (sg1, sg2) <- fmap split . lift $ gets stdgen
  lift $ modify (\s -> s { stdgen = sg1 })
  return sg2

tryStuff :: [Solve a] -> Solve a
tryStuff xs = foldl mplus (MaybeT $ return Nothing) xs

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
                       | otherwise         = Nothing 
unify t (Var (MVar x)) | not (x `occur` t) = Just $ M.singleton x t
                       | otherwise         = Nothing 
unify (Var x) (Var y) | x == y = Just idSub
unify (App f ts) (App f' ss) | f == f' = unifyTerms ts ss
unify (Const c) (Const d) | c == d = Just idSub
unify _ _ = Nothing

occur :: MVar -> Term -> Bool
occur x (Var (MVar y)) = x == y
occur x (Var (GVar _ xs)) = x `elem` xs
occur x (Var _) = False
occur x (App _ ts) = any (occur x) ts
occur x (Const _) = False

getMetas :: Formula -> [MVar]
getMetas = nub . goF
  where
    phi +++ psi = goF phi ++ goF psi

    goF Top = []
    goF Bot = []
    goF (Imp phi psi) = phi +++ psi
    goF (Rel _ ts)    = concatMap goT ts
    goF (Neg phi)     = goF phi
    goF (And phi psi) = phi +++ psi
    goF (Or phi psi)  = phi +++ psi
    goF (ForAll v f)  = goV v ++ goF f
    goF (Exists v f)  = goV v ++ goF f
    
    goT (Const _)  = []
    goT (Var v)    = goV v
    goT (App _ ts) = concatMap goT ts
    
    goV (UVar _)    = []
    goV (MVar m)    = [m]
    goV (GVar _ ms) = ms

testFormula :: Formula -> Maybe Deduction
testFormula f = evalState (runMaybeT (solve empty (f =>+ empty)))
  $ SS { nextVar = 0, nextMeta = 0, metaRestrictions = M.empty, stdgen = mkStdGen 42}

build :: Deduction -> (Ctx , Ctx)
build ded = case ded of
  Intro g d -> (g , d)
  LBot g d -> (g , d)
  RTop g d -> (g , d)
  RImp a b x -> let (g,d) = build x
                 in (a -: g , (a ~> b) =>+ (b -: d))
  LImp a b x1 x2 -> let (g1 , d1) = build x1
                        (g2 , d2) = build x2
                     in ((a ~> b) +=> (g1 +:+ (b -: g2))
                         , (a -: d1) +:+ d2)
  REqu a b x1 x2 -> let (g1 , d1) = build x1
                        (g2 , d2) = build x2
                     in ((a -: g1) +:+ (b -: g2)
                        , (a <~> b) =>+ ((b -: d1) +:+ (a -: d2)))
  LEqu a b x1 x2 -> let (g1 , d1) = build x1
                        (g2 , d2) = build x2
                     in ((a <~> b) +=> ((a -: b -: g1) +:+ g2) 
                        , d1 +:+ (a -: b -: d2))
  RNeg a x -> let (g , d) = build x
               in (a -: g, (Neg a) =>+ d)
  LNeg a x -> let (g , d) = build x
               in ((Neg a) +=> g, a -: d)
  RAnd a b x1 x2 -> let (g1, d1) = build x1
                        (g2, d2) = build x2
                     in (g1 +:+ g2
                        ,(And a b) =>+ (a -: d1) +:+ (b -: d2))
  ROr a b x      -> let (g, d) = build x
                     in (g, (Or a b) =>+ (b -: (a -: d)))
  LAnd a b x     -> let (g, d) = build x
                     in ((And a b) +=> (a -: (b -: g)), d)
  LOr a b x1 x2  -> let (g1, d1) = build x1
                        (g2, d2) = build x2
                     in ((Or a b) +=> (a -: g1) +:+ (b -: g2)
                        ,d1 +:+ d2)
  RForAll i o x -> let (g,d) = build x
                   in (g, i =>+ (o -: d))
  LForAll i o x -> let (g,d) = build x
                   in (i +=> (o -: g),d)
  RExists i o x -> let (g,d) = build x
                   in (g, i =>+ (o -: d))
  LExists i o x -> let (g,d) = build x
                   in (i +=> (o -: g),d)

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

shuff :: [a] -> Solve [a]
shuff [] = return []
shuff xs = do
  sg <- getTheStdGen
  return $ shuffle' xs (length xs) sg

solve :: Ctx -> Ctx -> Solve Deduction
solve gamma delta = case () of
 -- TODO this is an optimisation (probably) that we should look into adding again
 --   _ | (f : _) <- S.toList is -> return $ Intro gamma delta
    _ -> do
      subst <- getMetaRestrictions
      let possible =  [ (id1 , sub) 
                | (id1, t1) <- S.toList (getPredicates gamma)
                , (id2, t2) <- S.toList (getPredicates delta)
                , id1 == id2
                , Just sub <- [unifyTerms t1 t2]
                ]
      let p' = filter fst $ map (\(_,s) -> (agree s subst,s)) possible
      if not (null p')
         then do
            p'' <- shuff p'
            addMetaRestriction (snd . head $ p'')
            return $ Intro gamma delta
         else solve' gamma delta 
  where
--    is = (gamma `S.intersection` delta)
    solve' gamma delta 
      | Just (i , delta') <- getGood delta = case i of
        Top     -> return $ RTop gamma delta
        Imp a b -> RImp a b `fmap` solve (a +=> gamma) (b =>+ delta')
        Neg a   -> RNeg a   `fmap` solve (a +=> gamma) delta'
        Or a b  -> ROr  a b `fmap` solve gamma         (a =>+ b =>+ delta')
        ForAll v f -> do
            v' <- getNextVar ms
            let o = subst v v' f
            RForAll i o `fmap` solve gamma (o =>+ delta')
      | Just (i , gamma') <- getGood gamma = case i of
        Bot     -> return $ LBot gamma delta
        Neg a   -> LNeg a   `fmap` solve gamma'               (a =>+ delta)
        And a b -> LAnd a b `fmap` solve (a +=> b +=> gamma') delta
        Exists v f -> do
            v' <- getNextVar ms
            let o = subst v v' f
            LExists i o `fmap` solve (o +=> gamma') delta
      | Just (i , delta') <- getGoodSplit delta = case i of
        And a b -> RAnd a b `fmap` solve gamma (a =>+ delta')
                              `ap` solve gamma (b =>+ delta')
        Equiv a b -> REqu a b `fmap` solve (a +=> gamma) (b =>+ delta')
                                `ap` solve (b +=> gamma) (a =>+ delta')
      | Just (i , gamma') <- getGoodSplit gamma = case i of
        Or  a b -> LOr  a b `fmap` solve (a +=> gamma') delta
                              `ap` solve (b +=> gamma') delta
        Imp a b -> LImp a b `fmap` solve gamma' (a =>+ delta)
                              `ap` solve (b +=> gamma') delta
        Equiv a b -> LEqu a b `fmap` solve (a +=> b +=> gamma') delta
                                `ap` solve gamma' (a =>+ b =>+ delta)
      | otherwise = shuff toTry >>= tryStuff
      where
        ms = concatMap getMetas (S.toList $ on S.union ctxToSet gamma delta)
        toTry :: [Solve Deduction]
        toTry = 
             [ do 
               v' <- getNextMVar
               let o = subst v v' f
               p <- solve (o +=> gamma) delta
               return $ LForAll i o p | i@(ForAll v f) <- S.toList (getBad gamma)]
          ++ [ do 
               v' <- getNextMVar
               let o = subst v v' f
               p  <- solve gamma (o =>+ delta)
               return $ RExists i o p | i@(Exists v f) <- S.toList (getBad delta)]

dblNeg = Neg (Neg (Rel "P" [])) ~> Rel "P" []
scomb = let (p, q, r) = (Rel "P" [],Rel "Q" [], Rel "R" [])
  in (p ~> q ~> r) ~> (p ~> q) ~> p ~> r
swapF = let (p, q, r) = (Rel "P" [], Rel "Q" [], Rel "R" [])
  in (p ~>q ~> r) ~> q ~> p ~> r

natti = ((Rel "N" [Const "0"]) `And` (ForAll "x" $ (Rel "N" ["x"]) ~> Rel "N" [App "S" ["x"]])) ~> Rel "N" [App "S" [App "S" [Const "0"]]]

