module JavaLib where

import Data.List (intersperse)


data JVisibility = JPublic | JPrivate | JProtected

data JClassModifier = JAbstract | JInterface  | JClassFinal

data JModifier = JFinal | JStatic

type NumGenerics = Int
type UnqualifiedClassName = String

data JType = JInt | JChar | JString | JFloat | JDouble
           | JArray JType | JBoolean | JVoid | JClassType JClassName
           | JGeneric NumGenerics

data JClassName = JClassName UnqualifiedClassName NumGenerics
                | JGenericClassName UnqualifiedClassName [JType]

data JVarDecl = JVarDecl (String, JType)

data JVar = JDeclVar JVarDecl 
          | JParamVar JVarDecl 
          | JThisVar JVarDecl

data JParam = JVarParam JVar
            | JTypeValueParam JTypeValue
            | JExprParam JExpr

data JInstance = JVarInstance JVar
               | JNewInstance JType [JParam]

data JStmt = JAssignExpr JVar JExpr 
           | JAssignVar JVar JVar
           | JReturn JExpr 
           | JThrow JExpr

data JTypeValue = JIntValue Integer 
                | JBooleanValue Bool
                | JCharValue Char
                | JStringValue String
                | JFloatValue Float
                | JDoubleValue Double
                | JVoidValue

type MethodName = String

data JExpr = JNewExpr JType [JParam]
           | JValueExpr JTypeValue
           | JInstanceOfExpr JVar JType
           | JCallExpr JExpr MethodName [JParam]
           | JSumExpr JExpr JExpr
           | JSubExpr JExpr JExpr
           | JMultExpr JExpr JExpr
           | JDivExpr JExpr JExpr
           | JEqExpr JExpr JExpr
           | JNotEqExpr JExpr JExpr
           | JOrExpr JExpr JExpr
           | JAndExpr JExpr JExpr
           | JGreaterExpr JExpr JExpr
           | JGreaterEqExpr JExpr JExpr
           | JLowerExpr JExpr JExpr
           | JLowerEqExpr JExpr JExpr
           | JNotExpr JExpr

-- TODO: missing description = ClassName<generics>
data JClass = JClass { kname :: String, 
                       kgenerics :: Int,
                       kextends :: Maybe JClassName,
                       kimplements :: [String],
                       kvis :: JVisibility, -- klass visibility
                       kmodifiers :: [JClassModifier], -- klass modifiers
                       kbody :: [JClassBody]
                     }

data JClassBody = JAttribute { atvar :: JVarDecl, atvis :: JVisibility, atmodifiers :: [JModifier] }
                                | JMethod { methname :: String, methvis :: JVisibility, methmodifiers :: [JModifier], methparams :: [JVarDecl], methret :: JType, methbody :: [JStmt] }
                                | JConstructor { cname :: String, cvis :: JVisibility, cparams :: [JVarDecl], cbody :: [JStmt] }
                                | JStaticBlock { sbbody :: [JStmt] }

instance Show JVisibility where
	show = showVis

showVis :: JVisibility -> String
showVis JPublic = "public"
showVis JPrivate = "private"
showVis JProtected = "protected"

instance Show JClassModifier where
	show = showClassMod

showClassMod :: JClassModifier -> String
showClassMod JAbstract = "abstract"
showClassMod JInterface = "interface"
showClassMod JClassFinal = "final"

showList' sep [] = showString ""
showList' sep (x:xs) = shows x . if null xs then showString "" else showString sep . showList' sep xs

instance Show JModifier where
  show = showMod
  showList = showList' " "

showMod :: JModifier -> String
showMod JFinal = "final"
showMod JStatic = "static"

instance Show JClassName where
  show (JClassName name n) = name ++ (listGenerics n)
  show (JGenericClassName name ts) = name ++ generics
    where generics = if null ts then "" else "<" ++ sepByCommas (map (qualifyClassName . show) ts) ++ ">"

replace x y = map (\c -> if c == x then y else c)
qualifyClassName = replace '/' '.'
unqualifyClassName = replace '.' '/'

internalClassName JInt = "java/lang/Integer"
internalClassName JChar = "java/lang/Character"
internalClassName JBoolean = "java/lang/Boolean"
internalClassName JString = "java/lang/String"
internalClassName JVoid = "java/lang/Void"
internalClassName JFloat = "java/lang/Float"
internalClassName JDouble = "java/lang/Double"
internalClassName a@(JArray t) = arrayDimension a
internalClassName (JClassType jcn) = show jcn
internalClassName (JGeneric n) = [(toGeneric n)] ++ ""

arrayDimension :: JType -> String
arrayDimension (JArray t) = "[" ++ arrayDimension t
arrayDimension x = internalClassName x

toGeneric n = toEnum (n+65)
listGenerics 0 = ""
listGenerics numGenerics = "<" ++ sepByCommas (map (\x -> [toGeneric x]) [0..numGenerics-1]) ++ ">"

sepByCommas [] = ""
sepByCommas xs = foldl1 (\x y -> x ++ ","++ y) xs

instance Show JType where
	show = internalClassName

instance Show JVarDecl where
  show = showVarDecl
  showList = showList' ","

instance Show JVar where
  show = showJVar
  showList = showList' ", "

showJVar (JDeclVar (JVarDecl (n,t))) = n
showJVar (JParamVar (JVarDecl (n,t))) = n
showJVar (JThisVar (JVarDecl (n,t))) = "this." ++ n

instance Show JParam where
  show (JVarParam v) = show v
  show (JTypeValueParam v) = show v
  show (JExprParam e) = show e
  showList = showList' ", "

instance Show JStmt where
  show = showJStmt
  showList [] = showString ""
  showList (x:xs) = shows x . if null xs then showString ";" else showString ";" . showList xs

showJStmt (JAssignExpr v1 e1) = show v1 ++ " = " ++ show e1
showJStmt (JAssignVar v1 v2) = show v1 ++ " = " ++ show v2
showJStmt (JReturn e) = "return " ++ show e
showJStmt (JThrow e) = "throw " ++ show e

instance Show JExpr where
  show = showJExpr

showJExpr (JNewExpr t vars) = "new " ++ show t ++ "(" ++ show vars ++ ")"
showJExpr (JValueExpr v) = show v
-- Just to dont show the () around JCallExpr inside JCallExpr, like:
-- ((new Blah()).apply(x)).apply(...)
showJExpr (JCallExpr e@(JNewExpr t vars) mn params) = "(" ++ show e ++ ")" ++ "." ++ mn ++ "(" ++ show params ++")"
showJExpr (JCallExpr e mn params) = show e ++ "." ++ mn ++ "(" ++ show params ++")"
showJExpr (JSumExpr e1 e2) = show e1 ++ " + " ++ show e2
showJExpr (JSubExpr e1 e2) = show e1 ++ " - " ++ show e2
showJExpr (JMultExpr e1 e2) = "(" ++ show e1 ++ ") * " ++ show e2
showJExpr (JDivExpr e1 e2) = "(" ++ show e1 ++ ") / " ++ show e2
showJExpr (JEqExpr e1 e2) = "(" ++ show e1 ++ ") == (" ++ show e2 ++")"
showJExpr (JNotEqExpr e1 e2) = "(" ++ show e1 ++ ") != (" ++ show e2 ++")"
showJExpr (JNotExpr e1) = "!(" ++ show e1 ++ ")"
showJExpr (JOrExpr e1 e2) = "(" ++ show e1 ++ ") || (" ++ show e2 ++")"
showJExpr (JAndExpr e1 e2) = "(" ++ show e1 ++ ") && (" ++ show e2 ++")"
showJExpr (JGreaterExpr e1 e2) = "(" ++ show e1 ++ ") > (" ++ show e2 ++")"
showJExpr (JGreaterEqExpr e1 e2) = "(" ++ show e1 ++ ") >= (" ++ show e2 ++")"
showJExpr (JLowerExpr e1 e2) = "(" ++ show e1 ++ ") < (" ++ show e2 ++")"
showJExpr (JLowerEqExpr e1 e2) = "(" ++ show e1 ++ ") <= (" ++ show e2 ++")"

-- TODO implement showJExpr for instanceof

instance Show JTypeValue where
  show = showJTypeValue

showJTypeValue (JIntValue x) = show x
showJTypeValue (JBooleanValue x) = if x == True then "true" else "false"
showJTypeValue (JCharValue x) = "'" ++ [x] ++ "'"
showJTypeValue (JStringValue x) = show x
showJTypeValue (JFloatValue x) = show x
showJTypeValue (JDoubleValue x) = show x
showJTypeValue (JVoidValue) = ""

instance Eq JClass where
  (JClass {kname=x1}) == (JClass {kname=x2}) = x1 == x2

instance Show JClass where
	show = showClass
	showList = showList' "\n\n"

instance Show JClassBody where
	show = showClassBody

showStmts [] = ""
showStmts (s:ss) = show s ++ "; " ++ showStmts ss

showClass a = vis ++ " " ++ mods ++ " class " ++ cname ++ generics ++ extends ++ implements ++ " {" ++ cbody ++ "}"
  where vis = show $ kvis a
        mods = showClassMods $ kmodifiers a
        cname = kname a
        extends = tmp $ kextends a
          where tmp (Just className) = " extends " ++ (show className)
                tmp Nothing = ""
        cbody = showClassBodies $ kbody a
        implements = if null $ kimplements a then "" else foldl1 (\x y -> x ++ ","++ y) (kimplements a)
        generics = if kgenerics a == 0 then "" else "<" ++ foldl1 (\x y -> x ++ ","++ y) (map (\x -> [toGeneric x]) [0..(kgenerics a)-1]) ++ ">"

showClassMods [] = ""
showClassMods (x:xs) = showClassMod x ++ " " ++ showClassMods xs

showClassBodies [] = ""
showClassBodies (x:xs) = show x ++ "; " ++ showClassBodies xs

showClassBody (JAttribute {atvis=y,atvar=x}) = show y ++ " " ++ show x

showClassBody (JConstructor {cvis=cv, cname=cn, cparams=cp, cbody=cb}) =
    show cv ++ " " ++ cn ++ "(" ++ show cp ++ ") {" ++ show cb ++ "}"

showClassBody m@(JMethod {methname=mname}) = vis ++ " " ++ mods ++ " " ++ ret ++ " " ++ mname ++ "(" ++ params ++ ") {" ++ body ++ "}"
  where vis = show $ methvis m
        mods = show $ methmodifiers m
        ret = show $ methret m
        params = show $ methparams m
        body = show $ methbody m

showVarDecl (JVarDecl (s, t)) = qualifyClassName $ show t ++ " " ++ s
