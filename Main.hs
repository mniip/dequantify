{-# OPTIONS_GHC -fno-warn-tabs #-}
import Control.Arrow
import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Char
import Data.Function
import Data.List
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.Traversable
import qualified Data.Set as S
import Data.Set (Set)
import Debug.Trace
import System.Environment
import System.Exit
import Control.Monad.State
import Control.Monad.Trans.Free

type Parser b t a = FreeT ((->) t) b a
token :: Monad b => Parser b t t
token = FreeT . return . Free $ FreeT . return . Pure
parseStream :: Monad b => (s -> b (t, s)) -> Parser b t a -> s -> b (a, s)
parseStream next = runStateT . iterTM (StateT next >>=)
	where
		iterTM :: (Functor f, Monad m, MonadTrans t, Monad (t m)) => (f (t m a) -> t m a) -> FreeT f m a -> t m a
		iterTM f (FreeT m) = do
			val <- lift m
			case fmap (iterTM f) val of
				Pure x -> return x
				Free y -> f y
parseString :: MonadPlus b => Parser b t a -> [t] -> b (a, [t])
parseString = parseStream (maybe mzero return . uncons)
	where
		uncons (x:xs) = Just (x, xs)
		uncons _ = Nothing

occurences :: Eq a => a -> [a] -> Int
occurences x xs = length $ filter (== x) xs

type Poly v = [(Integer, [v])]

normalizePoly :: Ord v => Poly v -> Poly v
normalizePoly = filter ((/= 0) . fst) . map ((sum . map fst) &&& (snd . head)) . groupBy ((==) `on` snd) . sortBy (compare `on` snd) . map (fmap sort)

degree :: Eq v => v -> Poly v -> Int
degree v = foldr max 0 . map (occurences v . snd)

differentiate :: Ord v => v -> Poly v -> Poly v
differentiate v = normalizePoly . mapMaybe (diff v)
	where
		diff v (i, vs) = let l = occurences v vs
			in if l == 0
				then Nothing
				else Just (toInteger l * i, delete v vs)

dropFirst :: Ord v => v -> Poly v -> Poly v
dropFirst v ms = let l = degree v ms
	in filter ((/= l) . occurences v . snd) ms

takeFirst :: Ord v => v -> Poly v -> Poly v
takeFirst v ms = normalizePoly $ map (fmap (filter (/= v))) $ takeLead v ms

takeLead :: Ord v => v -> Poly v -> Poly v
takeLead v ms = let l = degree v ms
	in filter ((== l) . occurences v . snd) ms

multiplyPoly :: Ord v => Poly v -> Poly v -> Poly v
multiplyPoly ms ns = normalizePoly $ liftA2 mult ms ns
	where
		mult (i, vs) (j, ws) = (i * j, vs ++ ws)

scalePoly :: Integer -> Poly v -> Poly v
scalePoly i = map (\(j, vs) -> (i * j, vs))

addPoly :: Ord v => Poly v -> Poly v -> Poly v
addPoly ms ns = normalizePoly $ ms ++ ns

subPoly :: Ord v => Poly v -> Poly v -> Poly v
subPoly ms ns = normalizePoly $ ms ++ scalePoly (-1) ns

remainderPoly :: Ord v => v -> Poly v -> Poly v -> (Int, Poly v)
remainderPoly v ns ds = rem 0 v ds ns
	where
		rem n v ds [] = (n, [])
		rem n v ds rs
			| degree v ds > degree v rs = (n, rs)
			| otherwise = let t = map (fmap (\\ replicate (degree v ds) v)) $ takeLead v rs
				in rem (n + 1) v ds $ subPoly (multiplyPoly rs (takeFirst v ds)) (multiplyPoly t ds)

remPoly :: Ord v => v -> Poly v -> Poly v -> Poly v
remPoly v ns ds = snd $ remainderPoly v ns ds

comparablePoly :: Poly v -> Bool
comparablePoly = any $ not . null . snd

closedSet :: Ord v => v -> [Poly v] -> Set (Poly v)
closedSet v qs = go v S.empty qs
	where
		go v s [] = s
		go v s (q:qs)
			| q `S.member` s = go v s qs
			| scalePoly (-1) q `S.member` s = go v s qs
			| otherwise = go v (S.insert q s) $ dropFirst v q : takeFirst v q : differentiate v q : map (flip (remPoly v) q) (S.toList s) ++ map (remPoly v q) (S.toList s) ++ qs

data Sign = M | Z | P deriving (Eq, Show)

notSign :: Sign -> Sign
notSign M = P
notSign Z = Z
notSign P = M

data Diagram = Interval Sign | Root Diagram Sign Diagram deriving (Eq, Show)

notDiag :: Diagram -> Diagram
notDiag (Interval s) = Interval (notSign s)
notDiag (Root l s r) = Root (notDiag l) (notSign s) (notDiag r)

data RootSchema v = IntervalS | RootS (RootSchema v) (Poly v) (RootSchema v) deriving (Eq, Show)

data DiagTurn = L | R deriving (Eq, Show, Ord)
type DiagPath = [DiagTurn]

getDiag :: DiagPath -> Diagram -> Sign
getDiag _ (Interval s) = s
getDiag [] (Root _ s _) = s
getDiag (L:ps) (Root l _ _) = getDiag ps l
getDiag (R:ps) (Root _ _ r) = getDiag ps r

mergeSchema :: Poly v -> Diagram -> RootSchema v -> RootSchema v
mergeSchema p (Interval _) s = s
mergeSchema p (Root l _ r) s@IntervalS = RootS (mergeSchema p l s) p (mergeSchema p r s)
mergeSchema p (Root l _ r) (RootS l' p' r') = RootS (mergeSchema p l l') p' (mergeSchema p r r')

diagOf :: Ord v => Map (Poly v) Diagram -> Poly v -> Diagram
diagOf result p = case p `M.lookup` result of
	Just d -> d
	Nothing -> notDiag $ result M.! scalePoly (-1) p
				
buildDiag :: Ord v => v -> Set (Poly v) -> Map (Poly v) Sign -> (RootSchema v, Map (Poly v) Diagram)
buildDiag v polys init = foldr addDiag (IntervalS, M.empty) $ sortBy (flip compare `on` degree v) $ S.toList polys
	where
		signOf p = case p `M.lookup` init of
			Just s -> s
			Nothing -> notSign $ init M.! scalePoly (-1) p

		simpleSignOf [] = Z
		simpleSignOf [(k, [])] = if k > 0 then P else M
		simpleSignOf p = signOf p
	 
		addDiag p (sch, result) = let d = diag p
			in (mergeSchema p d sch, M.insert p d result)
			where
				diag [] = Interval Z
				diag [(k, [])] = Interval $ if k > 0 then P else M
				diag p | Just s <- p `M.lookup` init = Interval s
				diag p = let
						s = simpleSignOf $ takeFirst v p
					in if s == Z
						then diag (dropFirst v p)
						else let
								d = degree v p
								negInf = (if even d then id else notSign) $ simpleSignOf $ takeFirst v p
								posInf = simpleSignOf $ takeFirst v p
							in walk [] p negInf posInf sch

				walk _ _ ls rs IntervalS
					| ls == Z = Interval rs
					| rs == Z = Interval ls
					| ls == rs = Interval ls
					| otherwise = Root (Interval ls) Z (Interval rs)
				walk path p ls rs (RootS l q r) = let s = signAt (reverse path) p q in Root (walk (L:path) p ls s l) s (walk (R:path) p s rs r)

				signAt path p q = let s = simpleSignOf $ takeFirst v q
					in if s == Z
						then signAt path p (dropFirst v q)
						else let (d, r) = remainderPoly v p q in (if even d || s == P then id else notSign) $ path `getDiag` diagOf result r

data SignCriterion = Zero | NonZero | Negative | Positive | NonNegative | NonPositive deriving (Eq, Show)

testSign :: SignCriterion -> Sign -> Bool
testSign Zero = (== Z)
testSign NonZero = (/= Z)
testSign Negative = (== M)
testSign Positive = (== P)
testSign NonNegative = (/= M)
testSign NonPositive = (/= P)

mkCriterion :: Sign -> SignCriterion
mkCriterion Z = Zero
mkCriterion M = Negative
mkCriterion P = Positive

data Statement v = Equation (Poly v) SignCriterion | Statement v `And` Statement v | Statement v `Or` Statement v | Not (Statement v) | Taut | Absurd | Forall v (Statement v) | Exists v (Statement v) deriving (Eq, Show)

infixl 3 `And`
infixl 2 `Or`

evaluatePath :: Ord v => Statement v -> Map (Poly v) Diagram -> DiagPath -> Bool
evaluatePath Taut _ _ = True
evaluatePath Absurd _ _ = False
evaluatePath (And s t) m p = evaluatePath s m p && evaluatePath t m p
evaluatePath (Or s t) m p = evaluatePath s m p || evaluatePath t m p
evaluatePath (Not s) m p = not $ evaluatePath s m p
evaluatePath (Equation q c) m p = testSign c $ p `getDiag` diagOf m q

anyPath :: Ord v => Statement v -> Map (Poly v) Diagram -> RootSchema v -> Bool
anyPath = go []
	where
		go p s m IntervalS = evaluatePath s m (reverse p)
		go p s m (RootS l _ r) = evaluatePath s m (reverse p) || go (L:p) s m l || go (R:p) s m r

transformExists :: (Show v, Ord v) => v -> Statement v -> Statement v
transformExists v st = disjunct $ map conjunct $ findCells v st
	where
		conjunct = foldr And Taut . map (\(p, s) -> Equation p (mkCriterion s))
		disjunct = foldr Or Absurd

		findCells v st = let
				s = closedSet v (collectPolys st [])
				int = filter comparablePoly $ filter ((== 0) . degree v) $ S.toList s
			in filter (satisfiable s) $ traverse (\x -> map ((,) x) [M, Z, P]) int	
		
		collectPolys Taut = id
		collectPolys Absurd = id
		collectPolys (And s t) = collectPolys s . collectPolys t
		collectPolys (Or s t) = collectPolys s . collectPolys t
		collectPolys (Not s) = collectPolys s
		collectPolys (Equation q _) = (q:)

		satisfiable s cell = let (sch, m) = buildDiag v s (M.fromList cell) in anyPath st m sch

evalTrivial :: Statement v -> Bool
evalTrivial Taut = True
evalTrivial Absurd = False
evalTrivial (And s t) = evalTrivial s && evalTrivial t
evalTrivial (Or s t) = evalTrivial s || evalTrivial t
evalTrivial (Not s) = not $ evalTrivial s
evalTrivial (Equation [] c) = testSign c Z
evalTrivial (Equation [(k, [])] c) = testSign c (if k > 0 then P else M)
evalTrivial _ = error "Nontrivial statement"

possible :: (Show v, Ord v) => Statement v -> Bool
possible s = evalTrivial $ foldr transformExists s $ S.toList $ collectVars s S.empty
	where
		collectVars Taut = id
		collectVars Absurd = id
		collectVars (And s t) = collectVars s . collectVars t
		collectVars (Or s t) = collectVars s . collectVars t
		collectVars (Not s) = collectVars s
		collectVars (Equation q _) = S.union $ S.fromList (concatMap snd q)

optimize' :: (Show v, Ord v) => Statement v -> Statement v
optimize' Taut = Taut
optimize' Absurd = Absurd
optimize' (And s t) = case optimize s of
	Taut -> optimize t
	Absurd -> Absurd
	s -> case optimize t of
		Taut -> s
		Absurd -> Absurd
		t -> if possible (s `And` Not t)
			then if possible (t `And` Not s)
				then And s t
				else t
			else s
optimize' (Or s t) = case optimize s of
	Taut -> Taut
	Absurd -> optimize t
	s -> case optimize t of
		Taut -> Taut
		Absurd -> s
		t -> if possible (s `And` Not t)
			then if possible (t `And` Not s)
				then Or s t
				else s
			else t
optimize' (Not s) = case optimize s of
	Taut -> Absurd
	Absurd -> Taut
	s -> Not s
optimize' s = s

optimize :: (Show v, Ord v) => Statement v -> Statement v
optimize s = case optimize' s of
	s -> if possible s
		then if possible (Not s)
			then s
			else Taut
		else Absurd

showPoly :: Show v => Poly v -> String
showPoly = firstplus . concat . map fmt
	where
		fmt (1, x@(_:_)) = '+' : mono x
		fmt (-1, x@(_:_)) = '-' : mono x
		fmt (k, x)
			| k > 0 = '+' : show k ++ mono x
			| otherwise = show k ++ mono x
		mono x = filter (/= '\"') $ show x
		firstplus ('+':s) = s
		firstplus s = s

showStatement :: Show v => Statement v -> String
showStatement = go 0
	where
		parens True s = '(':s ++ ")"
		parens False s = s

		go _ Taut = "Tautology"
		go _ Absurd = "Absurd"
		go _ (Equation p c) = showPoly p ++ ' ':showCriterion c
		go d (And l r) = parens (d > 3) $ go 3 l ++ " && " ++ go 3 r
		go d (Or l r) = parens (d > 2) $ go 2 l ++ " || " ++ go 2 r
		go _ (Not s) = '!':go 4 s

showCriterion :: SignCriterion -> String
showCriterion Zero = "= 0"
showCriterion NonZero = "!= 0"
showCriterion Negative = "< 0"
showCriterion Positive = "> 0"
showCriterion NonNegative = ">= 0"
showCriterion NonPositive = "<= 0"

char :: (Eq t, MonadPlus b) => t -> Parser b t t
char x = mfilter (== x) token

word :: (Eq t, MonadPlus b) => [t] -> Parser b t [t]
word [] = return []
word (x:xs) = (:) <$> char x <*> word xs

arvar :: Parser [] Char (Poly Char)
arvar = (\x -> [(1, [x])]) <$> mfilter isAlpha token <|> (char '(' *> arsum <* char ')')

arnumber :: Parser [] Char (Poly Char)
arnumber = (\x -> [(read x, [])]) <$> some (mfilter isDigit token)

arunit :: Parser [] Char (Poly Char)
arunit = arvar <|> arnumber

arterm :: Parser [] Char (Poly Char)
arterm = (char '-' *> (scalePoly (-1) <$> arterm)) <|> foldr id <$> arunit <*> many ((multiplyPoly <$ char '*') <*> arunit <|> multiplyPoly <$> arvar)

arsum :: Parser [] Char (Poly Char)
arsum = foldr id <$> arterm <*> many (((addPoly <$ char '+') <|> (flip subPoly <$ char '-')) <*> arterm)

lgeq :: Parser [] Char (Statement Char)
lgeq = (\p c q -> Equation (subPoly p q) c) <$> arsum <*> lgcrit <*> arsum

lgcrit :: Parser [] Char SignCriterion
lgcrit = Zero <$ char '=' <|> NonZero <$ word "!=" <|> Negative <$ char '<' <|> Positive <$ char '>' <|> NonNegative <$ word ">=" <|> NonPositive <$ word "<="

lgunit :: Parser [] Char (Statement Char)
lgunit = (Not <$ char '!' <*> lgunit) <|> (Forall <$ word "forall" <|> Exists <$ word "exists") <*> mfilter isAlpha token <* char '.' <*> lgsum <|> lgeq <|> char '(' *> lgsum <* char ')'

lgterm :: Parser [] Char (Statement Char)
lgterm = foldl (flip id) <$> lgunit <*> many ((flip And <$ word "&&") <*> lgunit)

lgimp :: Parser [] Char (Statement Char)
lgimp = Or <$> (Not <$> lgterm) <* word "->" <*> lgimp <|> lgterm

lgsum :: Parser [] Char (Statement Char)
lgsum = foldl (flip id) <$> lgimp <*> many ((flip Or <$ word "||") <*> lgimp)

readStatement :: String -> Statement Char
readStatement s = case parseString lgsum $ filter (not . isSpace) s of
	(e, []):_ -> e
	_ -> error "Bad parse"

dequantify :: (Show v, Ord v) => Statement v -> Statement v
dequantify (And s t) = And (dequantify s) (dequantify t)
dequantify (Or s t) = Or (dequantify s) (dequantify t)
dequantify (Not s) = Not (dequantify s)
dequantify (Exists v s) = transformExists v $ dequantify s
dequantify (Forall v s) = Not $ transformExists v $ Not $ dequantify s
dequantify s = s

main = do
	args <- getArgs
	inter (showStatement . (if "--noopt" `elem` args then id else optimize) . dequantify . readStatement)
	where
		inter f = do
			l <- handle (\e -> (e :: SomeException) `seq` exitFailure) getLine
			putStrLn (f l)
			inter f
