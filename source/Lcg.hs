module Lcg (lcg,lcgn,lcgi) where

import Type
import TIMonad
import Scheme
import Subst

lcg:: [Scheme] -> TI Type
lcg scs = do (t, _) <- lcg' scs []; return t

-----------------------------------------------------------------------------
type Gen = [((Type,Type),Tyvar)]

lcg':: [Scheme] -> Gen -> TI (Type, Gen)
lcg' [sc]    s = do t <- freshInst sc; return (t,s)
lcg' (sc:scs) s = do ts <- mapM freshInst scs
                     (t',s') <- lcgn' ts s
                     t0 <- freshInst sc
                     (t,s'') <- lcgp t0 t' s'
                     return (t,s'')
lcg' []      _ = error "Lcg: empty list"

-----------------------------------------------------------------------------
lcgp:: Type -> Type -> Gen -> TI (Type,Gen)
lcgp t1 t2 s = 
  case lookup (t1,t2) s of
    Just a  -> return (TVar a, s)
    Nothing -> lcgp' t1 t2 s

lcgp':: Type -> Type -> Gen -> TI (Type, Gen)
lcgp' t1@(TVar (Tyvar _ _)) t2                    s = do TVar a <- freshTVar; return (TVar a, ((t1,t2),a):s)
lcgp' t1                    t2@(TVar (Tyvar _ _)) s = do TVar a <- freshTVar; return (TVar a, ((t1,t2),a):s)
lcgp' t1@(TCon (Tycon id1)) t2@(TCon (Tycon id2)) s
  | id1==id2  = return (t1,s)
  | otherwise = do TVar a <- freshTVar
                   return (TVar a, ((t1,t2),a):s)
lcgp' t1@(TAp t1a t1r)      t2@(TAp t2a t2r)      s =
  do (ta,s1) <- lcgp t1a t2a s
     (tr,s2) <- lcgp t1r t2r s1
     return (TAp ta tr, s2)
lcgp' t                     t'                    s = do TVar a <- freshTVar; return (TVar a, ((t,t'),a):s)
   
-----------------------------------------------------------------------------
lcgn:: [Type] -> TI Type
lcgn ts = do (t, _) <- lcgn' ts []; return t

lcgn':: [Type] -> Gen -> TI (Type,Gen)
lcgn' [t]        s = return (t,s)
lcgn' [t1, t2]   s = lcgp t1 t2 s
lcgn' (t1:t2:ts) s = do (ta,s1) <- lcgn' ts s; (tb,s2) <- lcgp t1 t2 s1; lcgp ta tb s2

-----------------------------------------------------------------------------
	       
lcgS::	[Type] -> [Subst] -> TI [Type]
lcgS ts ss = do (ts,_) <- lcgS' ts ss []; return ts

lcgS' []      _  s = return ([],s)
lcgS' ts      [] s = return (ts,s)
lcgS' (t: ts) ss s =
 do (t1,s1) <- lcgn' ([ apply sj t | sj <- ss]) s
    (ti,s2)  <- lcgS' ts ss s1
    return (t1: ti, s2)

-----------------------------------------------------------------------------

lcgi:: [Type] -> TI (Maybe Type)
lcgi [] = return Nothing
lcgi ts = do t <- lcgn ts; return (Just t)