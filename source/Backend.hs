module Backend where

import Char (toUpper)
import Data.List (zipWith4, zipWith, inits, nub, intersperse)
-- import qualified Control.Exception as Exception

import Assump
import Expr
import Literal
import Type
import TIMain
import Parser
import Predefs
import Scheme
import JavaLib

type GenericInfo = (String, Int)
type ConstantInfo = (String, Literal)
type IdIndexedTypCtx = [(String, Assump)]

data TransInfo = TransInfo { tiTypCtx :: IdIndexedTypCtx,
                             tiClasses :: [JClass], 
                             tiGenerics :: [GenericInfo],
                             tiConstants :: [ConstantInfo],
                             tiExprs :: [JExpr],
			     tiDebug :: [String]
                           }

instance Show TransInfo where
  show t@(TransInfo {tiTypCtx=tc}) = "Classes:\n" ++ show (tiClasses t) ++
                                     "\nConstants:\n" ++ show (tiConstants t) ++
                                     "\nExprs:\n" ++ show (tiExprs t) ++
				     "\nDebug:\n" ++ (concat $ map (++"\n") (tiDebug t)) ++ "\n"

data MTransInfo a = MTransInfo (TransInfo -> (TransInfo, a))

instance Monad MTransInfo where
    return result = MTransInfo ( \state -> (state, result) )
    (MTransInfo m) >>= f = MTransInfo ( \oldti -> let (newti, x) = m oldti; MTransInfo fx = f x in fx newti )

runMTransInfo :: TransInfo -> MTransInfo a -> a
runMTransInfo initState (MTransInfo m) = result where (_, result) = m initState

getTransInfo = MTransInfo (\state -> (state,state))
putTransInfo newstate = MTransInfo (\_ -> (newstate, ()))
modTransInfo f = do ti <- getTransInfo
		    putTransInfo (f ti)

debug :: String -> MTransInfo ()
debug s = do modTransInfo (\ti -> ti { tiDebug = (tiDebug ti) ++ [s] })

translateProgram filename = 
  do
    bg <- parseProgramFromFile filename
    case bg of
      Left err -> 
        do putStrLn ("Error when parsing: " ++ (show err))
           return ()
      Right bg -> 
        do
           let r = runMTransInfo (initTransInfo idIndexedTypCtx gi) $ translate flattenedBg
           putStrLn $ show r
           return ()
        where typCtx = (tiProgram predef bg)
	      idIndexedTypCtx = indexTypCtxById typCtx
              flattenedBg = flattenBg bg
              gi = getGenericInfo $ getDataDecls flattenedBg

initTransInfo :: IdIndexedTypCtx -> [GenericInfo] -> TransInfo
initTransInfo typCtx gi = TransInfo {tiTypCtx=typCtx, tiClasses=[], tiGenerics=gi, tiConstants=[], tiExprs=[], tiDebug=[]}

indexTypCtxById :: TypCtx -> IdIndexedTypCtx
indexTypCtxById = map (\assump -> (assump_id assump, assump))
  where assump_id ((Id ai _) :>: _) = ai

indexClassesByName :: [JClass] -> [(String, JClass)]
indexClassesByName = map (\jc -> (kname jc, jc))

flattenBg :: BindGroup -> [Impl]
flattenBg (expls,impls) = (map (\(i,s,a) -> (i,a)) expls) ++ impls

-- Data declarations have just one alternative
getDataDecls :: [Impl] -> [Assump]
getDataDecls [] = []
getDataDecls ((id, ((pats, Const assump):[])):impls) = [assump] ++ getDataDecls impls

getGenericInfo :: [Assump] -> [GenericInfo]
getGenericInfo [] = []
getGenericInfo (x:xs) = nub $ giDatatype : giConstructor : (getGenericInfo xs)
  where giDatatype = (,) (dataTypeName $ last assump_types) ngenerics
        giConstructor = (,) constrName ngenerics
        assump_types = getAssumpTypes x
        ngenerics = numGenerics assump_types
        (Id constrName _) :>: _ = x

translate :: [Impl] -> MTransInfo TransInfo
translate bs = do mapM translateBg bs
                  ti <- getTransInfo; 
                  return $ ti

translateBg :: (Id, [Alt]) -> MTransInfo ()
translateBg (id, (alts)) = if length alts > 1 then translateAlts id alts else translateAlt id (head alts)

translateAlts :: Id -> [Alt] -> MTransInfo ()
translateAlts id alts = undefined

toJTypeValue :: Literal -> JTypeValue
toJTypeValue (LitInt x) = JIntValue x
toJTypeValue (LitChar x) = JCharValue x
toJTypeValue (LitStr x) = JStringValue x
toJTypeValue (LitFloat x) = JDoubleValue x

toJExpr :: Expr -> JExpr
toJExpr (Const ((Id ":" _) :>: _)) = JNewExpr (JClassType $ JClassName "ConsF1" 1) []
toJExpr (Const ((Id "[]" _) :>: _)) = JNewExpr (JClassType $ JClassName "Nil" 1) []
toJExpr (Ap e1@(Var (Id "negate" _)) lit) = negate' $ toJExpr lit
  where negate' (JValueExpr (JIntValue x)) = JValueExpr $ JIntValue (-x)
        negate' (JValueExpr (JFloatValue x)) = JValueExpr $ JFloatValue (-x)
        negate' (JValueExpr (JDoubleValue x)) = JValueExpr $ JDoubleValue (-x)
        negate' _ = error "negate on a non-numeric value."
toJExpr (Ap e1@(Ap (Var (Id "+" _)) e11) e2) = JSumExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "-" _)) e11) e2) = JSubExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "*" _)) e11) e2) = JMultExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "/" _)) e11) e2) = JDivExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "==" _)) e11) e2) = JEqExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "/=" _)) e11) e2) = JNotEqExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "&&" _)) e11) e2) = JAndExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "||" _)) e11) e2) = JOrExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id ">" _)) e11) e2) = JGreaterExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "<" _)) e11) e2) = JLowerExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id ">=" _)) e11) e2) = JGreaterEqExpr (toJExpr e11) (toJExpr e2)
toJExpr (Ap e1@(Ap (Var (Id "<=" _)) e11) e2) = JLowerEqExpr (toJExpr e11) (toJExpr e2)
toJExpr e1@(Ap (Var (Id "not" _)) e11) = JNotExpr (toJExpr e11)
toJExpr (Ap e1 e2) = JCallExpr (toJExpr e1) "apply" [JExprParam $ toJExpr e2]
toJExpr (Var (Id "[]" _)) = JNewExpr (JClassType $ JClassName "Nil" 1) []
toJExpr (Var (Id "True" _)) = JValueExpr $ JBooleanValue True
toJExpr (Var (Id "False" _)) = JValueExpr $ JBooleanValue False
toJExpr (Lit x) = JValueExpr $ toJTypeValue x
toJExpr a = error $ "Unsupported expr : " ++ (show a)


altClosure :: String -> [JType] -> JType -> JType -> [JClassBody]
--altClosure name attribs ta tb = closureAttribs ++ methApply
--  where closureAttribs
altClosure name attribs ta tb = undefined

translateAlt :: Id -> Alt -> MTransInfo ()

translateAlt (Id id' _) (pats, e@(Ap e1 e2)) = 
  do debug $ "translating function " ++ id'
     ti <- getTransInfo
     let (Just infType) = lookup id' $ tiTypCtx ti
     let infTypes = getAssumpTypes infType
     let funParamTypes = take ((length infTypes) - 1) infTypes
     let funRetType = last infTypes
     let numClosures = length pats
     let closureNames = take numClosures $ altClosureNames id'
     debug $ "the inf type is " ++ (show infType)
     debug $ "param types: " ++ (show funParamTypes)
     debug $ "ret type: " ++ (show funRetType)
     debug $ "closures: " ++ (show closureNames)
     modTransInfo (\ti -> ti {tiExprs = [toJExpr e] ++ (tiExprs ti)})

translateAlt (Id id' _) (pats, Lit lit) = 
  do ti <- getTransInfo
     let uniqConstants = nub (tiConstants ti ++ [(id', lit)])
     putTransInfo (ti {tiConstants = uniqConstants})

-- THINK Generate the Fun class?
translateAlt (Id id' _) (pats, Const assump) = 
  do 
     ti <- getTransInfo
     let a = dataTypeMapping : constrMapping : (generateClosures id' dtName (updateWithGenerics (tiGenerics ti) mappedTypes) ngenerics)
     putTransInfo (ti {tiClasses = nub $ (tiClasses ti) ++ a})
  where assump_types = getAssumpTypes assump
        mappedTypes = map type2java assump_types
        dtName = dataTypeName $ last assump_types
        ngenerics = numGenerics assump_types
        constrAttribs = take ((length assump_types) - 1) $ mappedTypes
        dataTypeMapping = JClass {kname=dtName, kgenerics=ngenerics, kextends=Nothing, kimplements=[], kvis=JPublic, kmodifiers=[JAbstract], kbody=[]}
        constrMapping = JClass {kname=dtConstrName, kgenerics=ngenerics, kextends=Just $ JClassName dtName ngenerics, kimplements=[], kvis=JPublic, kmodifiers=[], kbody=(dcBody dtConstrName constrAttribs)}
        dtConstrName = id'

translateAlt id alt = error ("unsupported alternative: " ++ show alt)

updateWithGenerics :: [GenericInfo] -> [JType] -> [JType]
updateWithGenerics gts [] = []
updateWithGenerics gts (t@(JClassType (JClassName name _)):ts) = (updatedType $ lookup name gts) : (updateWithGenerics gts ts)
  where updatedType (Just n) = JClassType $ JClassName name n
        updatedType _ = t
updateWithGenerics gts (t:ts) = t : updateWithGenerics gts ts

numGenerics :: [Type] -> Int
numGenerics ts = (length . nub) (numTGens ts)
  where numTGens [] = []
        numTGens ((TGen n):ts) = n : numTGens ts
        numTGens ((TAp t1 t2):ts) = (numTGens [t1]) ++ (numTGens [t2]) ++ (numTGens ts)
        numTGens (_:ts) = numTGens ts

dataTypeName :: Type -> String
dataTypeName (TCon (Tycon (Id name _))) = name
dataTypeName (TAp t1 t2) = dataTypeName t1

{-
The data type:
  data Forma = Asda (Double,Double);
Generates:
  Forall (TAp (TAp (TCon (Tycon (->))) (TAp (TAp (TCon (Tycon (,,))) (TCon (Tycon Double))) (TCon (Tycon Double)))) (TCon (Tycon Forma)))
and this function returns:
  [TAp (TAp (TCon (Tycon (,,))) (TCon (Tycon Double))) (TCon (Tycon Double)),TCon (Tycon Forma)]

question: how to translate tuples?
-}
getAssumpTypes :: Assump -> [Type]
getAssumpTypes (id :>: (kd,Forall t)) = getSchemeTypes t

getSchemeTypes :: Type -> [Type]
getSchemeTypes (TAp (TAp (TCon (Tycon (Id "(->)" _))) t1) t2) = [t1] ++ getSchemeTypes t2
getSchemeTypes t = [t]

generateClosures :: String -> String -> [JType] -> Int -> [JClass]
generateClosures id dtName all_types ngenerics = mappingClosures
  where num_closures = (length all_types) - 1
        num_params = num_closures
        dcConstrName = id
        closureNames = closureName id num_closures
        closureName _ 0 = [dcConstrName]
        closureName id n = this_closure : closureName this_closure (n-1) -- TODO improve this... toUpper ...
          where this_closure = id ++ "F" ++ (show (num_closures - n + 1))
        mappedTypes = all_types
        mappingClosures = zipWith4 (\n p r t -> closureClass n ngenerics p r (closureClassBody n t p r)) closureNames mappedTypes (map (\cn -> JClassType $ JClassName cn ngenerics) (tail closureNames)) (inits mappedTypes)

dcBody :: String -> [JType] -> [JClassBody]
dcBody dcName dcAttribs = attribs ++ constructor
  where attribs = map attrib jvarAttribs
        attrib jv = JAttribute { atvar = jv, atvis = JPublic, atmodifiers = [] }
        jvarAttribs = jvarFields dcAttribs
        constructor = [ JConstructor {cvis=JPublic,cname=dcName,cparams=jvarAttribs, cbody=constrBody} ]
        constrBody = map (\x -> JAssignVar (JThisVar x) (JParamVar x)) jvarAttribs

closureClassBody :: String -> [JType] -> JType -> JType -> [JClassBody]
closureClassBody className types ta tb = attribs ++ constructor ++ methapply
  where attribs = map attrib jvarAttribs
        attrib jv = JAttribute { atvar = jv, atvis = JPublic, atmodifiers = [] }
        jvarAttribs = jvarFields types
        constructor = [ JConstructor {cvis=JPublic,cname=className,cparams=jvarAttribs, cbody=constrBody} ]
        constrBody = map (\x -> JAssignVar (JThisVar x) (JParamVar x)) jvarAttribs
        paramx = JVarDecl ("x", ta)
        methapply = [ JMethod { methname = "apply", methvis = JPublic, methmodifiers = [], 
          methparams = [paramx], methbody = [bodyApply], methret = tb } ]
        bodyApply = JReturn (JNewExpr tb $ map JVarParam (instanceParams ++ [JParamVar paramx]))
        instanceParams = map JThisVar jvarAttribs

closureClass :: String -> Int -> JType -> JType -> [JClassBody]  -> JClass
closureClass name ngenerics ta tb body = JClass { kname=name, kgenerics=ngenerics, kextends=Just $ JGenericClassName "Fun" [ta,tb], kimplements=[], kvis=JPublic, kmodifiers=[], kbody=body }

jvarFields :: [JType] -> [JVarDecl]
jvarFields jtypes = zipWith (\t n -> JVarDecl (n,t)) jtypes fieldNames

fieldNames :: [String]
fieldNames = map (\x -> "f"++ (show x)) [1..]

argNames :: [String]
argNames = map (\x -> "a"++ (show x)) [1..]

toUpperStr :: String -> String
toUpperStr = map toUpper

upperArgNames :: [String]
upperArgNames = map toUpperStr argNames

altClosureNames :: String -> [String]
altClosureNames prefix = map (camelCasePrefix ++) suffixes
  where camelCasePrefix = (toUpper $ head prefix) : tail prefix
        suffixes = map (foldl (++) "") (tail (inits $ upperArgNames))

type2java :: Type -> JType
type2java (TCon (Tycon (Id "Char" _))) = JChar
type2java (TCon (Tycon (Id "Bool" _))) = JBoolean
type2java (TCon (Tycon (Id "Int" _))) = JInt
type2java (TCon (Tycon (Id "Integer" _))) = JInt
type2java (TCon (Tycon (Id "Float" _))) = JFloat
type2java (TCon (Tycon (Id "Double" _))) = JDouble
type2java (TCon (Tycon (Id "()" _))) = JVoid
type2java (TCon (Tycon (Id "String" _))) = JString
type2java (TCon (Tycon (Id name _))) = JClassType $ JClassName name 0
type2java (TGen n) = JGeneric n
type2java a@(TAp t1 t2) = JClassType $ JClassName firstTypeName nGenerics
  where getTypes (TAp at1 at2) = (getTypes at1) ++ (getTypes at2)
        getTypes t = [t]
        firstTypeName = (\(TCon (Tycon (Id name _))) -> name) $ head theTypes
        nGenerics = numGenerics theTypes
        theTypes = getTypes a
type2java t = error $ "Unsupported type : " ++ (show t)
