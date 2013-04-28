module Expr where

import Assump
import Literal
import Type
import Pat
import Scheme

-- Binding Groups
type BindGroup = ([Expl], [Impl])
type Alt = ([Pat], Expr)
type Expl = (Id, Scheme, [Alt])
type Impl = (Id, [Alt])

-- Top-level Binding Groups
type Program = [BindGroup]

data Expr = Var Id 
		  | Lit Literal 
		  | Const Assump 
		  | Ap Expr Expr 
		  | Let BindGroup Expr 
		  | Lam Alt 
		  | If Expr Expr Expr
		  | Case  Expr [(Pat,Expr)]
		  deriving (Eq, Show)

type Rename = [(Id, Id)]

class Ren a where
  rename :: Rename -> a -> a

instance Ren Expr where
  rename r (Var i)       = case lookup i r of
							  Just i' -> Var i'
							  Nothing -> Var i
  rename r (Ap e1 e2)    = Ap (rename r e1) (rename r e2)
  rename r (Let b e)     = Let (rename r b) (rename r e)
  rename r (Lam a)       = Lam (rename r a)
  rename r (If e1 e2 e3) = If (rename r e1) (rename r e2) (rename r e3)
  rename r (Case e a)    = Case (rename r e) (rename r a) 
  rename r x             = x

instance (Ren a) => Ren [a] where
  rename r = map (rename r)

instance (Ren a, Ren b) => Ren (a,b) where
  rename r (a, b) = (rename r a, rename r b) 

instance (Ren a, Ren c) => Ren (a,b,c) where
  rename r (a, b, c) = (rename r a, b, rename r c) 

instance Ren Pat where
  rename r (PVar i)   = case lookup i r of
							  Just i' -> PVar i'
							  Nothing -> PVar i

  rename r (PCon a p) = PCon a (rename r p)
  rename r x          = x  

instance Ren Id where
  rename r i = case lookup i r of
					  Just i' -> i'
					  Nothing -> i

getRen :: Int -> BindGroup -> Rename 
getRen n (annot, inf) =  map ren ds  
  where 
	ds = (map (\(i,_, a) -> (i, a)) annot) ++ inf
	ren (Id i n', e) = (Id i n', Id i n) 

getBgIds (anns,infs) = (map (\(i,_,_) -> i) anns) ++ (map fst infs)
