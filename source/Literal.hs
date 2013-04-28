module Literal where

import Assump
import TIMonad
import Type

-- Literals
data Literal = LitInt   Integer 
			 | LitChar  Char 
			 | LitStr   String
			 | LitFloat Double
			 deriving (Eq, Show)

tiLit :: Literal -> TI (Type, TypCtx)
tiLit (LitInt   _) = return (tInt, [])
tiLit (LitChar  _) = return (tChar,[])
tiLit (LitStr   _)  = return (TAp tList tChar,[])
tiLit (LitFloat _) = return (tFloat, [])
