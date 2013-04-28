module TIMain where

import Char (isUpper)
import List((\\), intersect, union, nub)
import Monad (foldM)

import Assump
import Definitions
import Expr
import Literal
import Match
import Parser
import Pat
import Predefs
import Type
import TIMonad
import Scheme
import Subst
import Unify

-----------------------------------------------------------------------------
-- The following helper functions are used to construct sample programs; if we
-- change the representation of Expr above, then we need only change the
-- definitions of the following combinators to match, and do not need to
-- rewrite all the test code.

ap              = foldl1 Ap
evar v          = (Var v)
elit l          = (Lit l)
econst c        = (Const c)
elet g e        = foldr Let e (map toBg g)

toBg           :: [(Id, Maybe Scheme, [Alt])] -> BindGroup
toBg g          = ([(v, t, alts) | (v, Just t, alts) <- g ], 
                   [(v,alts)     | (v,Nothing, alts) <- g ])

pNil            = PCon nilC []
pCons x y       = PCon consC [x,y]

eNil            = econst nilC
eCons x y       = ap [ econst consC, x, y ]

ecase d as      = elet [[ (toid "_case", 	Nothing, [([p],e) | (p,e) <- as]) ]] (ap [evar (toid "_case"), d])

eif c t f       = If c t f
--eif c t f       = ecase c [(PCon trueC [], t),(PCon falseC [], f)] 

elambda alt     = elet [[ (toid "_lambda", 	Nothing, [alt]) ]] (evar (toid "_lambda"))

eguarded        = foldr (\(c,t) e -> eif c t e) efail

efail           = Const (toid "FAIL" :>: (CW, Forall (TGen 0)))

esign e t       = elet [[ (toid "_val", Just t, [([],e)]) ]] (evar (toid "_val"))

--eCompFrom p e c = ap [ econst bindM, e, elambda ([p],c) ]
eCompGuard e c  = eif e c eNil
eCompLet bgs c  = elet bgs c
eListRet e      = eCons e eNil

-----------------------------------------------------------------------------
tiExpr :: [Assump] -> Expr -> TI ((Type,TypCtx),InfCtx)

tiExpr g (Var i) 		  =  do {ty <- tc i g; return (ty, [])}

tiExpr g (Const (i:>:(oc, sc))) = do t <- freshInst sc
                                     (t1, g') <- tc i g
                                     let s   = unify (t, t1)
                                     return ((apply s t, apply s g'), [])

tiExpr _ (Lit l) 		= do {t <- tiLit l; return (t, [])}

tiExpr g0 (Ap e1 e2) 		= do ((t1,g1), i1) <- tiExpr g0 e1
				     ((t2,g2), i2) <- tiExpr g0 e2
				     a       <- freshTVar
				     let s0   = unify (t1, fn t2 a)
                                         g1' = apply s0 g1
                                         g2' = apply s0 g2
                                     let pts = types_of_common_lambda_bound_vars g1' g2'
                                     let s1  = unify (unzip pts)
                                         s   = s1 @@ s0
                                     return ((apply s a, apply s g1' `union` apply s g2'), applyInf s (i1++i2))


tiExpr g0 (Let bg e)		= do n <- freshNum 
                                     let r = getRen n bg
                                         bg' = rename r bg
                                         e'  = rename r e
                                     (infCtx, gb) <- tiBindGroup g0 bg' True
                                     ((t, g), infe') <- tiExpr gb e'
                                     let bg_is   = getBgIds bg'
                                         infCtx' = filter (\(i, _) -> i `elem` bg_is) infCtx
                                         gi      = bigUnion $ map (snd.snd) infCtx' 
                                         lbtv    = tv (lambda_bound_assumptions g)
                                     (s, g')     <- uniReqInf lbtv infCtx' g
                                     let s1 = unify $ unzip $ types_of_common_lambda_bound_vars g g'
                                         s2 = unify $ unzip $ types_of_common_lambda_bound_vars g gi
                                         s3 = unify $ unzip $ types_of_common_lambda_bound_vars g' gi
                                         ss = s3 @@ s2 @@ s1 @@ s
                                     return ((apply ss t, apply ss g' `union` apply ss g), applyInf ss (infCtx ++ infe'))
  where
   uniReqInf _ _ [] = return (nullSubst, [])
   uniReqInf vs i_ts (x:xs) = do (s,  g)  <- uri vs i_ts x 
                                 (ss, gs) <- uniReqInf vs i_ts xs 
                                 return (s @@ ss, g++gs)
   
   uri vs i_ts it@(i:>:(ot,sc)) = do case lookup i i_ts of
                                       Just ty@(t', g') -> do 
                                                             (t'', g'') <- freshTyping vs ty
                                                             t <- freshInst sc
                                                             let s   = unify (t, t'')
                                                                 g   = apply s g''                                                                 
                                                             return (s, g)
                                       Nothing         ->  return (nullSubst, [])

                                                                                     
tiExpr g (Lam alt) 		= tiAlt g alt

                                    
tiExpr g0 (If e e1 e2)        	= do ((t, g), i1)   <- tiExpr g0 e
                                     ((t1, g1),i2) <- tiExpr g0 e1
                                     ((t2, g2), i3) <- tiExpr g0 e2
                                     let s0  = unify (t, tBool)
                                         s1  = unify (t1, t2)
                                         pts1 = types_of_common_lambda_bound_vars g g1
                                         pts2 = types_of_common_lambda_bound_vars g g2 
                                         pts3 = types_of_common_lambda_bound_vars g1 g2
                                     let ss1  = unify (unzip pts1)
                                         ss2  = unify (unzip pts2)
                                         ss3 = unify (unzip pts3)
                                         ss = (((ss3 @@ ss2) @@ ss1) @@ s1) @@ s0 
                                     return ((apply ss t1, ((apply ss g) `union` (apply ss g1)) `union` (apply ss g2)), applyInf ss (i1++i2++i3)) 


{-tiExpr g0 (Case e0 branches) 	= do (t0, g) <- tiExpr g0 e0
				     v       <- freshTVar
				     let tiBr (t,g) (pat,e) = 
						do (t',g') <- tiPat g0 pat
						   let s  = unify (t,t')
						   (t'', g'') <- tiExpr (apply s g0 |+ apply s g') e
					           return (t'', apply s g  `union` apply s g'  `union` g'')
                                     foldM tiBr (v,g) branches-}
-----------------------------------------------------------------------------

-- type Alt = ([Pat], Expr) 

tiAlt :: TypCtx -> Alt -> TI (Typing, InfCtx)
tiAlt g0 (pats, e) 		=  do (ts,g1)     <- tiPats g0 pats
				      ((t,g),inf) <- tiExpr (g0 |+ g1) e
                                      pts         <- types_of_common_vars g g1
                                      let s   = unify $ unzip pts
				      return ((foldr fn (apply s t) (apply s ts), 
                                                apply s (g |- lb)), applyInf s inf)
    where 
       lb  = idsInPats pats
                                

tiAlts :: TypCtx -> [Alt] -> Type -> TI (Typing, InfCtx) 
tiAlts g0 alts t0 = foldM f ((t0,[]), []) alts
  where
    f ((t,g), inf) alt = do ((t',g'), inf') <- tiAlt g0 alt
     		            let s = unify (t,t')
		            return ((apply s t', apply s g  `union` apply s g'), applyInf s (inf ++ inf'))
-----------------------------------------------------------------------------

-- type InferType_bind = (Id, [Alt])


foldAlts g []     = return ([], [])
foldAlts g (a:as) = do t <- freshTVar 
                       (ty, inf)  <- tiAlts g a t
                       (tys,inf') <- foldAlts g as
                       return ((ty:tys), inf ++ inf') 
   
tiInferTyping :: TypCtx -> [Impl] -> TI InfCtx
tiInferTyping g0 bs             = do let (ids, altss) = (map fst bs, map snd bs)
                                     (typings, inf) <- foldAlts g0 altss
                                     return ((zip ids typings) ++ inf) 


-----------------------------------------------------------------------------

-- type AnnotType_bind = (Id, Scheme, [Alt])

checkAnnot :: [Expl] -> InfCtx -> TI InfCtx
checkAnnot [] ict = return ict
checkAnnot ((i, sc, alts):xs) ict 
  = do case lookup i ict of
         Just (t, g) -> do t' <- freshInst sc
                           if matchOk (t, t')  then 
                              do xs' <- checkAnnot xs ict
                                 let xs'' = filter (\(x, y) -> x /= i) xs'
                                 return ([(i, (t', g))]++xs'') 
                                else error ("Signature "++ show sc ++ " too general")
         Nothing     -> error  ("No definition for: " ++ (show i))

multdef g inf = case clashes idg idi of   
                     Just m  -> Just m
                     Nothing -> mult idi
   where
     clashes []     l = Nothing
     clashes (x:xs) l = if elem x l then Just x else clashes xs l
     mult    []       = Nothing
     mult    (x:xs)   = if elem x xs then Just x else mult xs          
     idg = map (\(i :>: _) -> i) g
     idi = (map fst) inf
-----------------------------------------------------------------------------

-- type BindGroup = ([AnnotType_bind], [InferType_bind])

tiBindGroup :: TypCtx -> BindGroup -> Bool -> TI (InfCtx, TypCtx)

-- unifying inferred with required types in inner binding groups is deferred
--          until the outermost binding group 
tiBindGroup g0 (annotatedType_bg,inferType_bg) inner = 

    do let g    = g0 |+ [ v:>:(CW,sc) | (v,sc,alts) <- annotatedType_bg ]
           infer_annot  = (inferType_bg ++ (map ( \ (i,_, a) -> (i, a)) annotatedType_bg))
       case multdef g0 infer_annot of  
            Just m  -> error ((show m) ++ " multiply defined")
            Nothing -> 
             do
                let infer_annot' = filter (not.isUpper.head.(\(i,_) -> show i)) infer_annot
                    const        = filter (isUpper.head.(\(i,_) -> show i)) infer_annot 
                is_const  <- tiInferTyping g const 
                is_const' <- unify_inf_req g is_const 
                let gc = infCtx2TypCtx is_const' 
                is_infTypings <- tiInferTyping (g |+ gc) infer_annot'
                if (inner) 
                  then return (is_infTypings, g)
                  else
                    do 
                       --is_infTypings'  <- debug "i_ts" is_infTypings (unify_inf_req (g |+ gc) is_infTypings)
                       is_infTypings'  <- unify_inf_req (g |+ gc) is_infTypings
                       is_infTypings'' <- checkAnnot annotatedType_bg is_infTypings'
                       return (is_infTypings'', g) 

-----------------------------------------------------------------------------

unify_inf_req:: TypCtx -> InfCtx -> TI InfCtx
unify_inf_req g is_infTypings
  = do let (is,infTypings) = unzip is_infTypings  -- [tau_i, Gamma_i]

       -- for each x:t in U Gamma_i find the corresponding x:ti in [xi:ti] (map fst infTypings)
       -- return a list of all such pairs (t,t_i)
           all_g_i = concat $ snd (unzip infTypings)
       tsReq_tsInf     <- foldM (getTs g is_infTypings)  [] (zip [0..] all_g_i)

       (tsReq_tsInf1,infCtx) <- unif_and_app g (tsReq_tsInf,is,infTypings)
       return (infCtx)  
 where
   unif_and_app g (tsReq_tsInf,is, infTypings) = 
    do let s           = unify $ unzip tsReq_tsInf
           infTypings' = apply s infTypings
       tsReq_tsInf'    <- foldM (getTs g (zip is infTypings')) [] 
                                (zip [0..] $ concat $ map snd infTypings')
       if stop s (map fst infTypings ++ 
                 (map ( \ (_ :>: (_, Forall t))-> t) $ concat $ map snd infTypings))
         then return (tsReq_tsInf',zip is infTypings')
         else if (circular_dep s ) -- tsReq_tsInf)
                  -- \xi test (see the paper)
                then error ("Cannot (semi-)unify inferred with required types\n" ++
                            "Well, one day we hope to give you better error messages... :-)" )
                else unif_and_app g (tsReq_tsInf',is,infTypings') 
   stop s ts = null (domain (filter ren s) `intersect` tv ts)
   ren ((Tyvar v _),(TVar (Tyvar v' _))) | v == v'   = False
                                         | otherwise = True  
   ren _ = True                              

-----------------------------------------------------------------------------

--getTs:: TypCtx -> InfCtx -> [(Type,Type)] -> (IneqIndex,Assump) -> TI [(Type,Type)]

-- getTs vs i_ts pts (n,i:>:sc) updates the list of pairs of types pts with pairs (t,t'), 
-- where t' = supInst vs n t'', for all i:t' \in i_ts, t''/=t (modulo renaming of tvars) 
-- vs indicate (free) type variables which shall not be quantified
--   (i.e.that occur in types of lambda-bound vars).
-- n corresponds to an inequality index in the underlying semi-unification problem
--   (please see the paper: http://www.dcc.ufmg.br/~camarao/sup/sup.pdf).
--   (getTs is called each time in a bg with distinct values of n, 
--    corresponding to distinct uses of a defined variable).

getTs g i_ts pts (n,i:>:(ot,sc)) = 
  do let getT (i,sc) = if ot == LB then return Nothing
                          else
                            case lookup i i_ts of
                              Just (t', g') -> let vs  = tv $ lambda_bound_assumptions g'
                                                   sc' = quantify (tv t') t' in 
                                               if sc==sc' 
                                                  then if null (vs `intersect` (tv t')) 
                                                          then return (Nothing) 
                                                          else error ("Expression " ++ (show i) ++ "\nExepected:" ++ (show sc) ++ "\nInferred :" ++ (show $ quantify (tv t'\\ vs) t'))
                                                  else do t'' <- supInst [] n t'; return (Just t'')
                              Nothing       -> if null (find i g) then error ("Undefined variable "++ (show i))
                                                  else return (Nothing)    
     maybe_t <- getT (i,sc)
     t <- freshInst sc 
     case maybe_t of
          Just t' -> return ((t,t') : pts)
          Nothing -> return pts 
                                                                                    
-----------------------------------------------------------------------------

circular_dep	:: Subst -> Bool
circular_dep    = fst . foldr circ (False,[])

circ		:: (Tyvar,Type) -> (Bool,Subst) -> (Bool,Subst)
circ _     (True,s)  = (True,s)
circ (u,t) (False,s) 
  | xi (TVar u) t'   = (True,s)
  | otherwise        = (False,(u,t'):s)
  where t' = apply' s t
        apply' s u@(TVar (Tyvar v (i:l)))  = 
           case lookup (Tyvar v l) s of
                Just t  -> t
                Nothing -> u 
        apply' s (TAp l r) = TAp (apply' s l) (apply' s r)
        -- apply' s t         = t
        apply' s t =  apply s t 

xi (TAp l r) (TAp l' r') = xi l l' || xi r r'
xi (TVar v)  (TAp l r)   = xi' v l || xi' v r
xi _          _          = False

xi' v           (TAp l r)            = xi' v l || xi' v r
xi' (Tyvar v l) (TVar (Tyvar v' l')) = v==v' && l `subStr` l'
xi' _           _                    = False

subStr	 		:: [Int] -> [Int] -> Bool
subStr [] _             = True
subStr l (_:l')         = l == l' || l `subStr` l'
subStr _  _             = False

tiProgram :: TypCtx -> BindGroup -> TypCtx
tiProgram g0 bgs  = infCtx2TypCtx $ runTI $ do {(i_t,g) <- tiBindGroup g0 bgs False; return (i_t)}

parseProgram filename = 
        do
                bg <- parseProgramFromFile filename
                case bg of
                        Left err -> 
                                do
                                        putStrLn ("Error: " ++ (show err))
                                        return []
                        Right bg -> return (tiProgram predef bg)
