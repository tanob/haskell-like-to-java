module Type where

-- Os identificadores sao strings
data Id = Id String Int deriving (Eq)

-- Types
data Type = TVar Tyvar
			| TCon Tycon
			| TAp Type Type
			| TGen Int
			deriving (Eq, Show)

data Tyvar = Tyvar String [Int] deriving (Eq, Show)

data Tycon = Tycon Id deriving (Eq, Show)

tChar  	 = TCon (Tycon $ toid "Char")
tBool    = TCon (Tycon $ toid "Bool")
tArrow 	 = TCon (Tycon $ toid "(->)")
tInt	 = TCon (Tycon $ toid "Int")
tInteger = TCon (Tycon $ toid "Integer")
tFloat	 = TCon (Tycon $ toid "Float")
tDouble	 = TCon (Tycon $ toid "Double")
tUnit  	 = TCon (Tycon $ toid "()")
tList	 = TCon (Tycon $ toid "[]")
tTuple n = TCon (Tycon $ toid (tupleN n))

infixr 4 `fn`
fn :: Type -> Type -> Type
a `fn` b = TAp (TAp tArrow a) b

tupleN n = "(" ++ (replicate n ',') ++ ")"

toid s = Id s 0

enumId :: Int -> String
enumId n = "v" ++ show n 


instance Show Id where
  show (Id s n) = if n == 0 then s else "let" ++ (show n) ++ "_" ++ s  

{-
instance Show Type where
  show = impstype 

instance Show Tyvar where
  show (Tyvar v l) = v ++ if null l then "" else "^" ++ show l 

instance Show Tycon where
  show (Tycon t) = show t

impstype (TAp t1 t2) = if t1 == (TCon (Tycon (toid "[]"))) then "[" ++ impstype t2 ++ "]" else
					   impstype2 t1 t2 
impstype (TVar t)    = show t
impstype (TCon t)    = show t
impstype (TGen i)    = [toEnum (i + 97)] ++ ""

impstype2 (TAp t1 t2) t3 = if t1 == (TCon (Tycon (toid "(->)"))) then impstypep t2 ++ " -> " ++ impstype t3 else 
						   if t1 == (TCon (Tycon (toid "(,)"))) then "(" ++ impstype t2 ++ "," ++ impstype t3 ++ ")" else
						   impstype3 t1 t2 t3
impstype2 t1 t2         =  impstype t1 ++ " " ++ impstype t2

impstype3 (TAp t1 t2) t3 t4 = if t1 == (TCon (Tycon (toid "(,,)"))) then "(" ++ impstype t2 ++ "," ++ impstype t3 ++ "," ++ impstype t4 ++")" else 
							  impstype t1 ++ " " ++ impstype t2 ++ " " ++ impstype t3 ++ " " ++ impstype t4
impstype3 t1 t2 t3 = impstype t1 ++ " " ++ impstype t2 ++ " " ++ impstype t3

impstypep t@(TAp (TAp t1 t2) t3) = if t1 == (TCon (Tycon (toid "(->)"))) then "(" ++ impstype t ++ ")" else impstype t 
impstypep t                      = impstype t

-}