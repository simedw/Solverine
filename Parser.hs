{-# LANGUAGE DoRec #-}
module Parser where

import Control.Applicative hiding (Const)
import Data.Parser.Grempa.Grammar 
import Data.Parser.Grempa.Dynamic

import CoreTypes
import qualified Lexar as L

parseString :: String -> Formula
parseString = parse parseFunDynamic . L.lexToks

parseFunDynamic :: Parser L.Tok Formula
parseFunDynamic = mkDynamicParser constrWrapper formula


formula :: Grammar L.Tok Formula
formula = do
  rec
    f <- rule
        [ Imp <@> f' <# L.Imp <#> f
        , id <@> f']
    f' <- rule
        [ paren f
        , ForAll <$> (UVar . L.fromTok) <@ L.Forall <#> L.var <#> f'
        , Exists <$> (UVar . L.fromTok) <@ L.Exists <#> L.var <#> f'
        , Neg <@  L.Not <#> f'
        , And <@> f' <# L.And <#> f'
        , Or  <@> f' <# L.Or <#> f'
        , id  <@> p]
    p <- rule
        [ Rel <$> L.fromTok <@> L.Pred "" <# L.LPar <#> terms <# L.RPar
        , (\x -> Rel (L.fromTok $ x) []) <@> L.Pred ""  ]
    term <- rule [ (Var . UVar . L.fromTok) <@> L.Var ""
                     , Const . L.fromTok <@> L.Const ""
                 , App <$> L.fromTok <@> L.Var "" <# L.LPar <#>  terms <# L.RPar]
    terms <- severalInter0 L.SemiColon term
  return f
  where 
     paren x = id <@ L.LPar <#> x <# L.RPar
  
{-
  F = P | Q Var . F | F -> F | F /\ F | F \/ F | ~ F | Top | Bot
  Q = forall | exists
  P = Predicate ( Terms ) | Term `P` Term
  Terms = Var | Fun ( Terms ) | Const
  Var = Char
-}