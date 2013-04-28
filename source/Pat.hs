module Pat where

import List (union)

import Assump
import Type
import Literal
import TIMonad
import Scheme
import Subst
import Unify

-- Patterns
data Pat = PVar Id 
			| PLit Literal 
			| PCon Assump [Pat]
			| PWildcard
			deriving (Eq, Show)

tiPat :: TypCtx -> Pat -> TI (Type, TypCtx)

tiPat _ (PVar i) =
	do 
		v <- freshTVar
		return (v, [i :>: (LB, toScheme v)])

tiPat _ (PLit l)          	  = tiLit l

tiPat g0 (PCon (i :>: (_,sc)) pats) = do 
									   (ts, g) <- tiPats g0 pats
									   t'      <- freshTVar
									   t1      <- freshInst sc
									   (t2, _) <- tc i g0
									   let 
									   	   s1 = unify (t1, t2)
										   s  = unify (apply s1 t2, foldr fn t' ts)  
										   ss = s @@ s1                                         
									   return (apply ss t', apply ss g)

tiPat _ PWildcard =
	do 
		v <- freshTVar
		return (v, [])

tiPats :: TypCtx -> [Pat] -> TI ([Type], TypCtx)
tiPats g pats = 
	do 
		qtsgshs <- mapM (tiPat g) pats
		let 
			ts = map fst qtsgshs
			gs  = map snd qtsgshs
		return (ts, bigUnion gs)


idsInPats = foldr ((**) . idsInPat) [] 
	where
		(**) :: [Id] -> [Id] -> [Id]
		[]     ** ids = ids
		[i]    ** ids = i:ids
		(i:is) ** ids = is ** (i:ids)

idsInPat (PVar id)     = [id]
idsInPat (PLit _)      = []
idsInPat (PCon _ pats) = idsInPats pats
idsInPat (PWildcard)   = []
