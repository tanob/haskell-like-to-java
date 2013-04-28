module Parser where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos

import List (sort)
import Char
import Debug.Trace

import Assump
import Definitions
import Expr
import Literal
import Pat
import Predefs
import Subst
import Scheme
import Type

haskellLangDef = haskellDef {
					reservedOpNames= ["::","=","->","@","\\", "<-", "..", ".", "|"]
					, reservedNames  = ["let","in","case","of","if","then","else",
										"data","type", "where"]
				 }

-- Para poder utilizar o analisador lexico do Parsec
lexer = P.makeTokenParser(haskellLangDef)

whiteSpace 	  = P.whiteSpace lexer
symbol 		  = P.symbol lexer
identifier 	  = P.identifier lexer
reserved 	  = P.reserved lexer
reservedOp 	  = P.reservedOp lexer
float		  = P.float lexer
natural 	  = P.natural lexer
charLiteral   = P.charLiteral lexer
stringLiteral = P.stringLiteral lexer

-- Definicoes para expressoes
exprTable = [[binary "." AssocRight], 
			 [negprefix "-"],
			 [binary "*" AssocLeft, binary "/" AssocLeft, binary "`div`" AssocLeft, binary "`rem`" AssocLeft, binary "`mod`" AssocLeft, binary "`quot`" AssocLeft],
			 [binary "+" AssocLeft, binary "-" AssocLeft],
			 [binCon ":" AssocRight, binary "++" AssocRight],
			 [binary "==" AssocNone, binary "/=" AssocNone, binary "<=" AssocNone, binary ">=" AssocNone, binary "<" AssocNone, binary ">" AssocNone], 
			 [binary "&&" AssocRight],
			 [binary "||" AssocRight],
			 [binary ">>" AssocLeft, binary ">>=" AssocRight]] 

binary n a = Infix (try (do {symbol n; return binOp})) a
				where binOp x y = Ap (Ap (Var (toid (justId n))) x) y

binCon n a = Infix (try (do {symbol n; return binOp})) a
				where binOp x y = Ap (Ap (Const (toid ":" :>: (CW, quantify [Tyvar "v1" []] ((TVar (Tyvar "v1" [])) `fn` TAp tList (TVar (Tyvar "v1" [])) `fn` TAp tList (TVar (Tyvar "v1" [])))))) x) y

negprefix n =  Prefix (try (do {symbol n; return unOp}))
				where unOp x = Ap (Var (toid "negate")) x

justId (c:cs) = if c /= '`' then (c:cs) else (rem cs)
		  where rem (c:cs) = if c == '`' then "" else (c:rem cs)

-- Analisa um arquivo
parseProgramFromFile :: Text.ParserCombinators.Parsec.Pos.SourceName
						-> IO
							 (Either
								Text.ParserCombinators.Parsec.Error.ParseError
								([Expl], [Impl]))
parseProgramFromFile = parseFromFile body

-- Regras
body = do { symbol "{"; ts <- topdecls; symbol "}"; return (concatBg (plainList ts)) }

topdecls =  topdecl `sepEndBy` (symbol ";")

topdecl = do { reserved "data"; st <- simpletype; symbol "="; cs <- constrs; return (concat (map (apCon st) cs)) }
		  <|> do { d <- decl; return d }

decl = try (do { g <- gendecl; return (map (\(i, p) -> (toid i, Just (quantify (tv [p]) p), [])) g) })
	   <|> try ( do { f <- funlhs; r <- rhs; return [(fst f, Nothing, [(snd f, r)])] } )
	   <?> "declaracao"

funlhs = do { v <- var; apats <- many apat; return (toid v, apats) }

rhs = do { symbol "="; e <- exp0; ds <- wdecls; return (apWdecls e ds) }
	-- tirado suporte a guardas
	
exp0 = try (do {e <- expi; ms <- maybeExps; return (apExpr e ms)})
	   <|> do {e <- exp10; ms <- maybeExps; return (apExpr e ms)}
	   
maybeExps = try (do {o <- qop; e <- expi; ms <- maybeExps; return ((toid o, e):ms)})
			<|> return []

expi = buildExpressionParser exprTable exp10

exp10 =  do {reserved "let"; d <- decls; reserved "in"; e <- expi; return (Let d e)}
		 -- <|> do {symbol "\\"; p <- apat; ps <- maybeapats; symbol "->"; e <- expi; return (Lam ((p:ps), e))}
		 -- <|> do {reserved "if"; e1 <- expi; reserved "then"; e2 <- expi; reserved "else"; e3 <- expi; return (If e1 e2 e3)}
		 -- <|> do {reserved "case"; e <- expi; reserved "of"; symbol "{"; as <- alts; symbol "}"; return (ecase e as)}
		 <|> do {reserved "do"; symbol "{"; s <- stmts; symbol "}"; return s}
		 <|> fexp

decls = do {symbol "{"; ds <- decl `sepEndBy` (symbol ";"); symbol "}"; return (concatBg $ plainList ds)}
		<|> return ([], [])
		
stmts = do {(p, s) <- stmt; s'<- maybestmts; return (apStmt p s s')}

maybestmts = do {symbol ";"; (p, s) <-stmt; s'<- maybestmts; return (Just (apStmt p s s'))}
			 <|> return Nothing

stmt = try (do {p <- pati; reservedOp "<-"; e <- exp0; return (Just p, Right e)})
	   -- <|> try (do {reserved "let"; d <- decls; return (Nothing, Left d)})
	   <|> try (do {e <- exp0; return (Nothing, Right e)})

fexp = do {e <- aexp; f <- fexp'; if f == [] then (return e) else return (foldl1 Ap (e:f))}

fexp' = try (do {e <- aexp; es <- fexp'; return (e:es)})
		<|> return []

aexp =  try (do {symbol "("; e <- exp0; symbol ")"; return e})  
		<|> try (do {symbol "("; e <- exp0; symbol ","; es <- aexps; symbol ")"; return (apTuple (e:es))})
		<|> try (do {symbol "("; o <- qop; symbol ")"; return (Var (toid o))})
		<|> try (do {symbol "["; e <- exp0; es1 <- maybeaexp; reservedOp ".."; es2 <- aexps; symbol "]"; return (apList' (e:es1 ++ es2))})
		<|> try (do {symbol "["; e <- exp0; symbol "]"; return (apList e)})
		<|> try (do {symbol "["; e <- exp0; symbol ","; es <- aexps; symbol "]"; return (apList' (e:es))})
		-- <|> try (do {symbol "["; e <- exp0; symbol "|"; e' <- qual e; symbol "]"; return (e')}) -- list comprehension
		<|> try (do {c <- gcon; return (Var (toid c))})
--        <|> do {c <- gcon; return (Const (c :>: (CW, toScheme (TVar (Tyvar "t0" [])))))}
		<|> do {i <- qvar; return (Var (toid i))} 
		<|> do {l <- literal; return (Lit l)}

aexps = do {e <- exp0; es <- maybeaexp; return (e:es)}
		<|> return []

maybeaexp = do {symbol ","; e <- exp0; es <- maybeaexp; return (e:es)}
			<|> return []

apat = try (do { symbol "("; p <- pati; symbol ")"; return p })
	   <|> try (do { symbol "("; p <- pati; symbol ","; pats <- sepBy1 pati (symbol ","); symbol ")"; return (apTuplep (p:pats)) })
	   <|> try (do {i <- var; return (PVar (toid i))})
	   <|> try (do { g <- gcon; return (PCon (toid g :>: (CW, Forall (TVar (Tyvar "v1" [])))) []) })
	   <|> do { lit <- literal; return (PLit lit) }
	   <|> do { symbol "_"; return PWildcard }
	   <|> do { symbol "["; pats <- sepBy1 pati (symbol ","); symbol "]"; return (apListp pats) }

pati = do { p <- pat10; m <- maybepati; return (apPat2 p m) }

maybepati = do { c <- qconop; p <- pati; return (Just (c, p)) }
		   <|> return Nothing

pat10 = try (do{ c <- gcon; ps <- many1 apat; return (apPat c ps ps) })
		 <|> do { p <- apat; return p }

-- [(var, type)]
gendecl = do { vars <- many1 var; symbol "::"; t <- type'; return (map (\v -> (v,t)) vars) }
		 <|> return []

simpletype = do { tc <- conid; tvs <- many tyvar; return (apSimpletype tc tvs) }

constrs = constr `sepBy1` (symbol "|")

-- (constr name, [type], [field name])
constr = try (do { t1 <- atype; c <- conop; t2 <- atype; return (c, (t1:[t2]), []) })
		 <|> try (do { c <- con; symbol "{"; fs <- many fielddecl; symbol "}"; return (c, map snd (plainList fs), map fst (plainList fs)) })
		 <|> try (do { c <- con; ts <- many atype; return (c, ts, []) })

-- [(var name, type)]
fielddecl = do { v <- (var `sepBy1` (symbol ",")); symbol "::"; t <- type'; return (zip (map toid v) (repeat t)) }

var = varid 
	  <|> do {symbol "("; v <- varsym; symbol ")"; return v }

conop = try (do { symbol "`"; c <- conid; symbol "`"; return c })
		<|> try consym

con = do { symbol "("; csym <- consym; symbol ")"; return csym }
	  <|> conid
	  
atype = try (do { t <- gtycon; return t })
		<|> try (do { symbol "("; t1 <- type'; symbol ","; t2 <- type'; ats <- many atype; symbol ")"; return (apTuplet (t1:(t2:ats))) })
		<|> do { symbol "("; t <- type'; symbol ")"; return t }
		<|> do { symbol "["; t <- type'; symbol "]"; return (TAp tList t) }
		<|> do { t <- tyvar; return (TVar t) }

gtycon = do { g <- qtycon; return g }
		 <|> do { symbol "["; symbol "]"; return tList }
		 <|> try (do { symbol "("; symbol ")"; return tUnit })
		 <|> try (do { symbol "("; symbol "-"; symbol ">"; symbol ")"; return tArrow })
		 <|> do { symbol "("; symbol ","; num_commas <- num_symbols ","; symbol ")"; return (tTuple (num_commas+1)) }

type' = buildExpressionParser [[Infix (do {symbol "->"; return (\x y -> x `fn` y)}) AssocRight]] btype

btype = do {t <- atype; ts <- many atype; return (if (ts == []) then t else (foldl1 TAp (t:ts)) )}

op = try (varop)
	  <|> conop

varop = try $ do {symbol "`"; i <- varid; symbol "`"; return i} 
		<|> try varsym

qtycon = tycon
tycon = do { c <- conid; return (TCon (Tycon $ toid c)) }
tyvar = do { i <- varid; return (Tyvar i []) }
qconid = conid 

conid = try $ do{ whiteSpace; name <- identifier;
		  if (isLower (head name) )
		  then unexpected ("Variable " ++ show (name))
		  else return (name)
		 }

varid = try $ do{ whiteSpace; name <- identifier;
		  if (isUpper (head name) )
		  then unexpected ("Constructor " ++ show (name))
		  else return (name)
		 }

consym = try $ do {symbol ":"; s <- symsOrColon; 
					if (isReservedOp (":"++s))
					  then unexpected ("reserved operator " ++ show (":"++s))
					 else return (":"++s)}

varsym = try $ do {s <- sym; ss <- symsOrColon;
					 if (isReservedOp (s++ss))
					  then unexpected ("reserved operator " ++ show (s++ss))
					 else return (s++ss)}

symsOrColon = do { ss <- many (try (sym) <|> symbol ":"); return (if (null ss) then [] else foldl1 (++) ss ) }

syms = do{ ss <- many1 sym; return (foldl1 (++) ss) }

sym = symbol "!" <|> symbol "#" <|> symbol "$" <|> symbol "%" <|> symbol "&" <|> symbol "*" 
	  <|> symbol "+" <|> symbol "." <|> symbol "/" <|> symbol "<" <|> symbol "=" <|> symbol ">" 
	  <|> symbol "?" <|> symbol "@" <|> symbol "\\" <|> symbol "^" <|> symbol "-" <|> symbol "~" 
	  <|> symbol "^" <|> symbol "|"

qcon = do {symbol "("; c <- gconsym; symbol ")"; return c}
	   <|> qconid

gconsym = try (qconsym)
		  <|> do {symbol ":"; return ":"}

qconsym = consym

literal = try (do {l <- float; return (LitFloat l)})
		   <|> do {l <- natural; return (LitInt l)}  
		   <|> do {l <- charLiteral; return (LitChar l)}
		   <|> do {l <- stringLiteral; return (LitStr l)}

gcon =  try (do { symbol "("; symbol ")"; return "()" })
		<|> try (do { symbol "("; symbol ","; num_commas <- num_symbols ","; symbol ")"; return (tupleN num_commas) })
		<|> do { symbol "["; symbol "]"; return "[]" }
		<|> do { t <- qcon; return t }

qconop = try $ do {symbol "`"; c <- qconid; symbol "`"; return c}
		 <|> try gconsym

qvarop = try $ do {symbol "`"; i <- qvarid; symbol "`"; return i} 
		<|> try qvarsym

qvarsym = varsym

qvarid = varid

qvar = var

qop = try (qvarop)
	  <|> try (qconop)

-- Helpers
num_symbols s = do { syms <- many (symbol s); return (length syms) }

{- Algumas funcoes como 'fielddecl', retornam listas, mas usando em conjunto com 'many'
teremos como retorno uma lista de listas, a funcao plainList soluciona isso, gerando uma lista
com todos os elementos dentro das sublistas. -}
plainList = foldl1 (++)

genField _ _ _ _ [] [] = []    
genField as p len i (t:ts) (v:vs) = (v, Nothing, [([genPat as p len], Var $ toid "x")]):genField as (p+1) len i ts vs

genPat as p len = PCon as ((replicate (p-1) PWildcard) ++ [PVar $ toid "x"] ++ (replicate (len-p) PWildcard))

apCon t (i, [], _)   = [(toid i, Nothing, [([], Const (toid i :>: (CW, quantify (tv t) t)))])]
apCon t (i, ts, [])  = [(toid i, Nothing, [([], Const (toid i :>: (CW, quantify (tv (t:ts)) (foldr1 fn (ts++[t])))))])]
apCon t (i, ts, vs) =  (toid i, Nothing, [([], Const as)]): (genField as 1 (length vs) i ts vs)
  where as = (toid i :>: (CW, quantify (tv (t:ts)) (foldr1 fn (ts++[t]))))

apSimpletype i [] = TCon (Tycon $ toid i)
apSimpletype i tvars = foldl1 TAp ((TCon (Tycon $ toid i)):t')
					where t' = map TVar tvars

tcPat n (_:[]) = (TVar (Tyvar ("t"++ (show n)) [])) `fn` (TVar (Tyvar "t0" [])) 
tcPat n (_:xs) = ((TVar (Tyvar ("t"++ (show n)) [])) `fn` (tcPat (n+1) xs))

apPat i ps = PCon (toid i :>: (CW, Forall t))
		  where t = tcPat 1 ps

apPat2 p1 (Just (c, p2)) = apPat c (p1:[p2]) (p1:[p2])
apPat2 p Nothing = p

apList e = Ap (Ap (Const consC) e) (Const nilC)
apListp [p]      = PCon consC [p, PCon nilC []]
apListp (p:ps)   = PCon consC [p, apListp ps]
apList' es = foldr1 (\x y -> Ap (Ap (Const consC) x) y) (es++[Const nilC])

apTuple (es) = foldl1 Ap ((Var $ toid (tupleN (length es))):es)
apTuplet (ts) = foldl1 TAp ((TCon (Tycon $ toid (tupleN (length ts)))):ts)
apTuplep ps = PCon (tupC (length ps)) ps

apStmt (Just p) (Right s) (Just s') = Ap (Ap (Var (toid ">>=")) s) (Lam ([p], s'))
apStmt Nothing  (Right s) (Just s') = Ap (Ap (Var (toid ">>")) s) s'
apStmt _ (Right s) Nothing          = s     
apStmt _ (Left d) (Just s')         = Let d s'
apStmt _ (Left _) Nothing           = error "Last generator in do {...} must be an expression" 

apWdecls e Nothing = e
apWdecls e (Just ds) = (Let ds e)

apExpr e [] = e
apExpr e ((o,e'):s) = apExpr (Ap (Ap (Var o) e) e') s

wdecls = do { reserved "where"; ds <- decls; return (Just ds) }
		 <|> return Nothing

concatBg [] = ([], [])
concatBg ((i,Nothing, a):ds) = if null (show i) then concatBg ds 
								 else let (es, is) = concatBg (dropBg i ds)
									  in (es, (i,a ++ (concatAlt $ takeBg i ds)):is)

concatBg ((i,Just t, a):ds) = let (es, is) = concatBg (dropBg i ds)
							  in ((i,t, a ++ (concatAlt $ takeBg i ds)):es, is)

takeBg i ds  = takeWhile (\(i', mt, a') -> i == i' && mt == Nothing) ds
dropBg i ds  = dropWhile (\(i', mt, a') -> i == i' && mt == Nothing) ds
concatAlt ds = concat (map trd' ds)


-- Necessario para implementar isReservedOp, uma vez que essa funcao eh privada da lib parsec
isReserved names name = scan names
		where
		  scan []       = False
		  scan (r:rs)   = case (compare r name) of
							LT  -> scan rs
							EQ  -> True
							GT  -> False

isReservedOp name = isReserved (sort (reservedOpNames haskellLangDef)) name
