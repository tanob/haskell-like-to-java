module TIMonad where

import Type
import Scheme


-----------------------------------------------------------------------------
newtype TI a = TI (FreshIndex -> (FreshIndex,a))

type FreshIndex = (Int,Int)             -- last fresh tyvar index so far

instance Monad TI where
  return x   = TI (\i -> (i,x))
  TI m >>= f = TI (\i -> let (i',x) = m i; TI fx = f x in  fx i')

runTI      	:: TI a -> a
runTI (TI m) 	= result where (_,result) = m (0,1) 

freshTVar	:: TI Type
freshTVar  	= TI (\(i,ii) -> let v = Tyvar (enumId i) [] in ((i+1,ii),TVar v))

freshInst	:: Scheme -> TI Type
freshInst (Forall t) = do ts <- mapM (\_ -> freshTVar) [0..maxTGen (-1) t]
                          return (inst ts t)

freshNum	:: TI Int
freshNum  	= TI (\(i,ii) -> ((i,ii+1),ii))

supInst		:: [Tyvar] -> Int -> Type -> TI Type
supInst lbvs n (TAp l r) = do t1 <- supInst lbvs n l 
                              t2 <- supInst lbvs n r
                              return $ TAp t1 t2
supInst lbvs n (t@(TVar tv@(Tyvar v l)))
  | tv `elem` lbvs	 = return t
  | otherwise      	 = return $ TVar $ Tyvar v (n:l)
supInst _    _ t         = return t

-----------------------------------------------------------------------------
class MaxTGen a where
  maxTGen:: Int -> a -> Int

instance MaxTGen Type where
  maxTGen n (TAp t1 t2) = maxTGen (maxTGen n t1) t2
  maxTGen n (TGen n')   = max n n'
  maxTGen n _           = n

instance MaxTGen a => MaxTGen [a] where
  maxTGen n = foldr f n 
    where f a n' = max (maxTGen n a) n'

-----------------------------------------------------------------------------
class Instantiate t where
  inst  :: [Type] -> t -> t
instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen i)  = ts !! i
  inst ts t         = t
instance Instantiate a => Instantiate [a] where
  inst ts           = map (inst ts)

-----------------------------------------------------------------------------
