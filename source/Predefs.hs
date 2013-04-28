module Predefs where

import Assump
import Definitions
import Type
import Scheme

-- Pre definitions
nilC	= toid "[]" :>: (CW, (Forall (TAp tList (TGen 0))))
consC	= toid ":"  :>: (CW, (Forall (TGen 0 `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))))
tupC n  = toid (tupleN n) :>: (CW, (Forall (foldr1 fn ((map (\x -> TGen x) [0..1]) ++ [foldl (\x y -> TAp x y) (tTuple (n-1)) (map (\x -> TGen x) [0..1])]))))

predef = [nilC, consC, tupC 2, tupC 3, tupC 4, tupC 5, tupC 7,
		  toid "." :>: (CW, Forall ((TGen 0 `fn` TGen 1) `fn` (TGen 2 `fn` TGen 0) `fn` TGen 2 `fn` TGen 1)),
		  toid "+" :>: (CW, Forall (tInt `fn` tInt `fn` tInt)),
		  toid "-" :>: (CW, Forall (tInt `fn` tInt `fn` tInt)),
		  toid "negate" :>: (CW, Forall (tInt `fn` tInt)),
		  toid "*" :>: (CW, Forall (tInt `fn` tInt `fn` tInt)),
		  toid "/" :>: (CW, Forall (tInt `fn` tInt `fn` tFloat)),
		  toid "div" :>: (CW, Forall (tInt `fn` tInt `fn` tInt)),
		  toid "mod" :>: (CW, Forall (tInt `fn` tInt `fn` tInt)), 
		  toid "<" :>: (CW, Forall (TGen 0 `fn` TGen 0 `fn` tBool)),
		  toid "<=" :>: (CW, Forall (TGen 0 `fn` TGen 0 `fn` tBool)),
		  toid ">" :>: (CW, Forall (TGen 0 `fn` TGen 0 `fn` tBool)),
		  toid ">=" :>: (CW, Forall (TGen 0 `fn` TGen 0 `fn` tBool)),
		  toid "==" :>: (CW, Forall (TGen 0 `fn` TGen 0 `fn` tBool)),
		  toid "&&" :>: (CW, Forall (tBool `fn` tBool `fn` tBool)),
		  toid "||" :>: (CW, Forall (tBool `fn` tBool `fn` tBool)),
		  toid "not" :>: (CW, Forall ((tBool `fn` tBool))),
		  toid "True" :>: (CW, Forall tBool),
		  toid "False" :>: (CW, Forall tBool),
		  toid "uncurry" :>: (CW, Forall ((TGen 0 `fn` TGen 1 `fn` TGen 2) `fn` TAp (TAp (tTuple 2) (TGen 0)) (TGen 1) `fn` TGen 2)),
		  toid "_concatMap" :>: (CW, (Forall (((TGen 0 `fn` TAp tList (TGen 1)) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 1))))),
		  toid "FAIL" :>: (CW, Forall (TGen 0))]
