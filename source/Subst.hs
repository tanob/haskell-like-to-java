module Subst where

import Prelude 
import List(nub, intersect, union)

import Type

type Subst  = [(Tyvar, Type)]

domain = map fst
range  = map snd

nullSubst  :: Subst
nullSubst   = []

(+->)      :: Tyvar -> Type -> Subst
u +-> t     = [(u, t)]

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

merge      :: Subst -> Subst -> Maybe Subst
merge s1 s2 = if agree then Just s else Nothing
 where s     = s1 ++ s2
       agree = all (\v -> apply s1 (TVar v) ==
                          apply s2 (TVar v))
                   (domain s1 `intersect` domain s2)

mergeAll = foldr cons (Just nullSubst)
  where cons (Just s) (Just s') = merge s s'
        cons _        _         = Nothing

-----------------------------------------------------------------------------
class Subs t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]

instance Subs Type where
  apply s (TVar u)  = case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply s t         = t

  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv t         = []

instance Subs a => Subs [a] where
  apply s     = map (apply s)
  tv          = nub . concat . map tv

instance (Subs a, Subs b) => Subs (a,b) where
  apply s (a,b) = (apply s a, apply s b)
  tv (a,b)      = tv a `union` tv b

-----------------------------------------------------------------------------


