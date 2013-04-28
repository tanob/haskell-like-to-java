module Scheme where

import Type
import Subst

-- Scheme
data Scheme = Forall Type deriving (Eq, Show)

quantify vs qt = Forall (apply s qt)
  where 
		vs' = [ v | v <- tv qt, v `elem` vs ]
		s   = zip vs' (map TGen [0..])

toScheme :: Type -> Scheme
toScheme t = Forall t

instance Subs Scheme where
  apply s (Forall t) = Forall (apply s t)
  tv (Forall t)      = tv t