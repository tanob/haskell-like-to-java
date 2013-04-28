module Match where

import Type
import Subst
import Unify

-----------------------------------------------------------------------------
class Match t where
  match :: (t,t) -> Maybe Subst

instance Match Type where
  match (TAp l r , TAp l' r') = do sl <- match (l,l')
                                   sr <- match (r,r')
                                   merge sl sr
                                   
  match (TCon tc1, TCon tc2 )
     | tc1==tc2               = Just nullSubst
     | otherwise              = Nothing
  match (TVar u  , t        ) = varBind u t -- was Just (u +-> t) 
  match (t1      , t2       ) = Nothing


instance Match t => Match [t] where
  match (ts,ts') = mergeAll (zipWith (curry match) ts ts')

-----------------------------------------------------------------------------
class MatchOk t where
  matchOk :: (t,t) -> Bool

instance MatchOk Type where
  matchOk (t1, t2) = case match (t1,t2) of
                          Just _  -> True
                          Nothing -> False {- error ("Matching\n" ++ (show t1) ++ 
                                            "\nwith\n" ++ (show t2)) -}
                                      
instance MatchOk t => MatchOk [t] where
  matchOk (ts,ts') =  and (zipWith (curry matchOk) ts ts')

-----------------------------------------------------------------------------
