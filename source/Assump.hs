module Assump where

import List hiding (find)

import Dom
import Lcg
import Subst
import Type
import Unify
import Scheme
import TIMonad

data Assump = Id :>: (Kind_of_defining_occurrence, Scheme)  -- notation: i :>: (kdo, sc)
     deriving (Eq, Show)

data Kind_of_defining_occurrence = OW | CW | LB deriving (Eq,Show)
                               -- open, closed, or lambda-bound defining occurrences
                               -- open assumptions are "assumed to exist somewhere, in an open world 
                               --   (are not "checked for satisfaction")
                               -- closed assumptions come from given definitions 

type TypCtx  = [Assump]        -- notation: g

-----------------------------------------------------------------------------

open_world (i :>: (OW, sc)) = True
open_world _                = False

instance Subs Assump where
  apply s (i :>: (kdo, sc)) = i :>: (kdo, apply s sc)
  tv (i :>: (kdo, sc))      = tv sc

find	:: Id -> TypCtx -> [(Kind_of_defining_occurrence, Scheme)]
find i g = [ (kdo, sc) | (i' :>: (kdo, sc)) <- g, i'==i ]

schemes_of i = (map snd) . find i

tc     	:: Id -> TypCtx -> TI (Type, TypCtx)
tc i g = if null ocs_scs
            then do t <- freshTVar 
                    return (t, [i :>: (CW, toScheme t)])
            else do t <- lcg $ map snd ocs_scs
                    return (t, map (i :>:) ocs_scs) -- `union` (g <|>* tv t)
  where ocs_scs = find i g

openWorld (OW,_) = True
openWorld _      = False

{-
-----------------------------------------------------------------------------
-- 
-- as <|> v is the restriction of a context as to a set of type vars v,
-- giving only those assumptions with variables in v.
--
-- as <|>* v is the closure of restricting a context as to (type vars) v, 
-- giving assumptions with type vars in v or in any included assumption.
--
-----------------------------------------------------------------------------

(<|>) :: [Assump] -> [Tyvar] -> [Assump]
as <|> v = foldr f [] as
  where f (i :>: (oc, t)) = if null (tv t `intersect` v) then id else ((i :>: (oc, t)):)

as <|>* v
  | null (v' \\ v) = as <|> v
  | otherwise      = as <|>* v'
  where v' = tv (as <|> v)
-}

-----------------------------------------------------------------------------
-- 
-- as |+ as' overrides assumptions of as with those in as' 
--
as |+ as' = as' ++ filter compl as
  where compl (i :>: __) = not (i `elem` (dom as'))

-----------------------------------------------------------------------------

instance Dom Assump where
  dom (i :>: _) = [i]

-----------------------------------------------------------------------------

bigUnion:: Eq a => [[a]] -> [a]
bigUnion = foldr (union) [] -- should be in List

-----------------------------------------------------------------------------

types_of_common_vars :: TypCtx -> TypCtx -> TI [(Type, Type)]
types_of_common_vars g0 g0' = do let freshInst' (i:>:(_,sc)) = do t <- freshInst sc; return (i,t)
                                 g  <- mapM freshInst' g0
                                 g' <- mapM freshInst' g0' 
                                 return [ (t, t') | (i,t) <- g, (i',t') <- g', i==i']

types_of_common_lambda_bound_vars :: TypCtx -> TypCtx -> [(Type, Type)]
types_of_common_lambda_bound_vars g g' = [ (t, t') | i :>: (LB,Forall t)  <- lambda_bound_assumptions g, 
                                                     i':>: (LB,Forall t') <- lambda_bound_assumptions g', i==i']

types_of_reincident_vars :: TypCtx -> TI [[Type]]
types_of_reincident_vars g = do let freshInst' (i:>:(oc,sc)) = do t <- freshInst sc; return (i,t)
                                g'  <- mapM freshInst' g
                                return (map (map snd) $ filter reincidents $ groupBy sameIds g')
  where
       sameIds (i,_) (i',_) = i==i'
       reincidents []  = False
       reincidents [x] = False
       reincidents _   = True

lambda_bound_assumptions = filter lambda_bound_assumption

lambda_bound_assumption (i :>: (LB,_)) = True
lambda_bound_assumption _              = False
-----------------------------------------------------------------------------

(|-) 	:: TypCtx -> [Id] -> TypCtx
g |- is 
                     -- filters out elements "is" in g, 
                     -- but checks that all elements in is occur in g only once
                     -- if not, reports an error.

  = if length (filter (==True) (map (`elem` is) (map (\ (i:>:_) -> i) g))) <= length g 
      then filter (\ (i:>:_) -> i `notElem` is) g
      else error ("This would need a predicative second-order lambda-calculus of rank 2 or more\n" ++
                  "               That is: parameter " ++ (show i) ++ " would need to have a polymorphic type for the program to be typeable.")
    where 
         i                = takeFirstNonSing $ groupBy (\ (i:>:sc) (i':>:sc') -> i==i') g
         takeFirstNonSing = (\ (i :>: _ ) -> i) . head . head 

     
-----------------------------------------------------------------------------
(|-|) 	:: TypCtx -> [Id] -> TypCtx
g |-| is  -- filters out elements "is" in g

  = filter (\ (i:>:_) -> i `notElem` is) g
     
-----------------------------------------------------------------------------

type Typing   = (Type, TypCtx)

type IdTyping = (Id, Typing) 
type InfCtx   = [IdTyping]

applyInf s = map (\(i, t) -> (i, apply s t))

-----------------------------------------------------------------------------

infCtx2TypCtx :: InfCtx -> TypCtx
infCtx2TypCtx = map close

close:: IdTyping -> Assump
close (i,(ti,gi)) = i:>: (CW, quantify (tv ti \\ tv (lambda_bound_assumptions gi)) ti)

infCtx2TypCtx' :: InfCtx -> TypCtx
infCtx2TypCtx' = map typing2assump  
  where
     typing2assump (i,(ti,gi)) = i:>: (CW, toScheme ti)

-------------------------------------------------------------------------------
freshTyping :: [Tyvar] -> Typing -> TI Typing
freshTyping lbtv (t, g) = do let ts = (tv t `union` tv g) \\ lbtv
                             ntv <- mapM (\_ -> freshTVar) [0..length ts]
                             let s = zip ts ntv
                             return (apply s t, apply s g)  