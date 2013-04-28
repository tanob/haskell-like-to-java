module Unify where

import Type
import Subst

-----------------------------------------------------------------------------
class Unify t where
  mgu :: (t,t) -> Maybe Subst

instance Unify Type where
  mgu (TAp l r,  TAp l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu (apply s1 r, apply s1 r')
                                 Just (s2 @@ s1) 
  mgu (t,        TVar u   ) = varBind u t
  mgu (TVar u,   t        ) = varBind u t
  mgu (TCon tc1, TCon tc2 )
             | tc1==tc2     = Just nullSubst
  mgu (t,t')                = Nothing 

unifyFails (t1,t2) = mgu (t1,t2) == Nothing

instance (Subs t, Unify t) => Unify [t] where
  mgu (x:xs, y:ys) = do s1 <- mgu (x,y)
                        s2 <- mgu (apply s1 xs, apply s1 ys)
                        return (s2 @@ s1)
  mgu ([]  , []  ) = return nullSubst
  mgu _            = Nothing

varBind :: Tyvar -> Type -> Maybe Subst

varBind u t | t == TVar u   = Just nullSubst
            | u `elem` tv t = Nothing
            | otherwise     = Just (u +-> t)

-----------------------------------------------------------------------------
class Unif t where 
  unify:: (t,t) -> Subst

instance Unif Type where
  unify (t,t') = case mgu (t,t') of
    Nothing -> error ("\nunification:         " ++ (show t) ++  
                      "\ndoes not unify with: " ++ (show t'))
    Just s  -> s

instance (Subs t, Unif t) => Unif [t] where
  unify (x:xs, y:ys) = let s1 = unify (x,y)
                           s2 = unify (apply s1 xs, apply s1 ys)
                       in (s2 @@ s1)
  unify ([]  , []  ) = nullSubst
  unify _            = nullSubst

-----------------------------------------------------------------------------

