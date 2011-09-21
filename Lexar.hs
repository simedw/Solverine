{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}                                 
module Lexar where

import Data.Data
import Data.Char
import Data.Parser.Grempa.Static
import Language.Haskell.TH.Lift
data Tok 
   = LPar | RPar
   | Imp | Or | And | Not
   | Forall | Exists
   | Var  { fromTok :: String }
   | Const  { fromTok :: String }
   | Pred { fromTok :: String }
   | SemiColon
  deriving (Show, Read, Eq, Ord , Typeable, Data)
   
$(deriveLift ''Tok)
instance ToPat Tok where toPat = toConstrPat 
   
   
var = Var ""
   
lexToks :: String -> [Tok]
lexToks [] = []
lexToks ('(':xs) = LPar : lexToks xs
lexToks (')':xs) = RPar : lexToks xs
lexToks (',':xs) = SemiColon : lexToks xs
lexToks ('-':'>':xs) =  Imp : lexToks xs
lexToks ('!':xs) =  Not : lexToks xs
lexToks ('~':xs) =  Not : lexToks xs
lexToks ('\\':'/':xs) = Or : lexToks xs
lexToks ('|':xs) = Or : lexToks xs
lexToks ('&':xs) = And : lexToks xs
lexToks ('/':'\\':xs) = And : lexToks xs
lexToks ('∃':xs) = Exists : lexToks xs
lexToks ('∀':xs) = Forall : lexToks xs
lexToks ('e':'x':'i':'s':'t':'s':xs) = Exists : lexToks xs
lexToks ('f':'o':'r':'a':'l':'l':xs) = Forall : lexToks xs
lexToks as@(a:rest) 
   | isLower a = go Var isId as
   | isNumber a = go Const isId as
   | isUpper a = go Pred isId as
   | otherwise = lexToks rest


isId :: Char -> Bool                                                                 
isId c = isAlphaNum c || c == '_' || c == '\''                                       
                                                                                     
isSym :: Char -> Bool                                                                
isSym '(' = False                                                                    
isSym ')' = False                                                                    
isSym c   = isPunctuation c || isSymbol c                                            
                                                                                       
go :: (String -> Tok) -> (Char -> Bool) -> String -> [Tok]                           
go c p xs = let (v, rest) = span p xs in c v : lexToks rest                          
                                                                 