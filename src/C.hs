{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module C where

import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.Type.Nat ( Nat(..), SNatI, toNatural )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Test.QuickCheck
import Common

-- A variable x_i in n dimensions where
-- i < n
-- varExp i means x^(i+1) to disallow zero-powers
data Var n = Var { varDim :: Fin n, varExp :: Nat } deriving (Eq, Ord)

instance Show (Var n) where
  show (Var n Z)    = "x_" <> show n -- no need to show exponent of one
  show (Var n e)  = "x_" <> show n <> "^" <> show (S e)

instance SNatI n => Arbitrary (Var n) where
  arbitrary = Var <$> elements (V.toList V.universe) <*> resize 4 arbitrary

evalVar :: Number -> Var n -> Number
evalVar n v = n ^ toNatural (S . varExp $ v)

evalVarAt :: Vec n Number -> Var n -> Number
evalVarAt vn v = evalVar (vn V.! varDim v) v

-- for constructing valid instances of Term
varDimEq :: Var n -> Var n -> Bool
varDimEq v1 v2 = varDim v1 == varDim v2

-- Product of two vars assuming dimensions are equal
-- +1 is because of the shifted representation for the exponents
varProd :: Var n -> Var n -> Var n
varProd (Var n1 exp1) (Var _ exp2) = Var n1 $ S exp1 + exp2


-- A product of variables with a coefficient
-- Explicit representation for a term where the
-- coefficient is zero, ie. Term vars 0 is not allowed
data Term n = ZeroTerm | Term [Var n] Number deriving (Eq, Ord)

instance Show (Term n) where
  show ZeroTerm    = show (mempty :: Number)
  show (Term [] d) = show d
  show (Term vs d) = "(" <> show d <> ")*" <> (L.intercalate "*" . fmap show $ vs)

-- the monoid action on term(s) is multiplication, not sum
instance Semigroup (Term n) where
  ZeroTerm <> _ = ZeroTerm
  _ <> ZeroTerm = ZeroTerm
  (Term vs d) <> (Term vs' d') = Term vs'' $ d*d' where
    vs'' = combineSimilar varDimEq varProd $ merge vs vs'

instance Monoid (Term n) where
  mempty = liftToTerm 1

instance SNatI n => Arbitrary (Term n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkTerm <$> resize 2 arbitrary <*> arbitrary

liftToTerm :: Number -> Term n
liftToTerm 0 = ZeroTerm
liftToTerm d = Term [] d

-- A 'smart constructor' that removes variables
-- when the coefficient is zero, combines variables
-- with same dimension and sorts the variables
-- in ascending order for simpler comparison and printing
mkTerm :: [Var n] -> Number -> Term n
mkTerm _  0 = ZeroTerm
mkTerm vs d = Term (combineSimilar varDimEq varProd . L.sort $ vs) d

evalTerm :: Vec n Number -> Term n -> Number
evalTerm _ ZeroTerm    = 0
evalTerm vn (Term vs d) = foldr (*) d $ fmap (evalVarAt vn) vs

-- Evaluates Var if it matches to Fin n, otherwise
-- simply adds it to terms
evalSpecificVar :: Number -> Fin n -> Var n -> Term n -> Term n
evalSpecificVar _  _   _ ZeroTerm    = ZeroTerm
evalSpecificVar vn dim v (Term vs d) = if varDim v == dim
  then Term vs $ d * evalVar vn v
  else Term (v:vs) d

-- evaluate variables where the dimension is Fin n
-- at the point speficied in the Vec
partialEvalTerm :: Number -> Fin n -> Term n -> Term n
partialEvalTerm _  _   ZeroTerm    = ZeroTerm
partialEvalTerm n dim (Term vs d) = foldr (evalSpecificVar n dim) (Term [] d) vs

-- needed to make C a group
negateTerm :: Term n -> Term n
negateTerm ZeroTerm    = ZeroTerm
negateTerm (Term vs d) = Term vs (negate d)

-- for constructing valid instances of C
termVarsEq :: Term n -> Term n -> Bool
termVarsEq t1 t2 = getVs t1 == getVs t2 where
  getVs ZeroTerm    = Nothing
  getVs (Term vs _) = Just vs

-- Product of two terms assuming the vars are equal
termSum :: Term n -> Term n -> Term n
termSum ZeroTerm    t           = t
termSum t           ZeroTerm    = t
termSum (Term vs d) (Term _ d') =
  if d + d' == 0 then ZeroTerm else Term vs $ d + d'


-- A sum of nonzero term(s), ie. polynomials as terms is of the form
-- a*x_i*...*x_j + bx_h*...*x_k + ...
newtype C n = Terms { cTerms :: [Term n] } deriving (Eq, Ord)

instance Show (C n) where
  show = (<>) "C: " . L.intercalate " + " . fmap show . cTerms

instance SNatI n => Arbitrary (C n) where
  arbitrary = mkC <$> resize 4 arbitrary

-- the monoid action is now sum, not product as with term
-- (this is because terms needs to be a semiring)
instance Semigroup (C n) where
                              --these are already ordered so a merge is enough
  cn <> cn' = sortedTermsIntoC $ merge (cTerms cn) (cTerms cn')

instance Monoid (C n) where
  mempty = liftToC ZeroTerm

-- Being (Abelian) Group and Semiring makes it a Ring
instance Group (C n) where
  ginv = mkC . fmap negateTerm . cTerms

-- this is the multiplication, kind of confusingly corresponding
-- to monoid action of term
instance Semirng (C n) where
  sappend cn cn' = mkC $ (<>) <$> cTerms cn <*> cTerms cn'

instance Semiring (C n) where
  sempty = liftToC . liftToTerm $ 1

instance Algebra (C n) where
  amult a = sappend (liftToC . liftToTerm $ a)

liftToC :: Term n -> C n
liftToC t1 = mkC [t1]

evalC :: Vec n Number -> C n -> Number
evalC vn = sum . fmap (evalTerm vn) . cTerms

-- evaluate terms in C where the dimension is Fin n
-- at the point specified in Vec
partialEvalCAt :: Vec n Number -> Fin n -> C n -> C n
partialEvalCAt vn dim = partialEvalC (vn V.! dim) dim

partialEvalC :: Number -> Fin n -> C n -> C n
partialEvalC n dim = mkC . fmap (partialEvalTerm n dim) . cTerms

-- A 'smart constructor' which ensures that the term(s)
-- are in correct order, terms with common variable-part are
-- summed together and and terms with coefficient 0 are filtered out
mkC :: [Term n] -> C n
mkC = sortedTermsIntoC . L.sort

sortedTermsIntoC :: [Term n] -> C n
sortedTermsIntoC = Terms
                 -- Remove 0s from the sum
                 . filter (ZeroTerm /=)
                 -- ax_1x_2 + bx_1x_2 = (a+b)x_1x_2 etc.
                 . combineSimilar termVarsEq termSum

-- d x^3 = 3x^2 etc.
partialDVar :: Fin n -> Var n -> Term n
partialDVar n v = case (n == varDim v, varExp v) of
  (False, _)        -> ZeroTerm
  (_    , Z)        -> liftToTerm 1
  (_    , (S exp')) -> Term [Var n exp'] $ fromIntegral (S (S exp'))

-- this works only because term can by construction contain
-- at most one term that has a nonzero partial derivative
partialDTerm :: Fin n -> Term n -> Term n
partialDTerm _ ZeroTerm                    = ZeroTerm
partialDTerm _ (Term [] _)                 = ZeroTerm
partialDTerm n (Term (v : vs) d) = case partialDVar n v of
  ZeroTerm -> Term [v] 1 <> partialDTerm n (Term vs d)
  t'       -> t' <> Term vs d

-- fold over the terms
partialD :: C n -> Fin n -> C n
partialD cn n = foldMap (liftToC . partialDTerm n) . cTerms $ cn

-- This could probably be simplified
antiDTerm :: Fin n -> Term n -> Term n
antiDTerm _ ZeroTerm           = ZeroTerm
antiDTerm n (Term []     coef) = Term [Var n Z] coef
antiDTerm n (Term (v:vs) coef) = case compare n $ varDim v of
  LT -> Term (Var n Z : v : vs) coef
  EQ -> let e = varExp v in Term (Var n (S e) : vs) (divNumber coef (toNatural . S . S $ e))
  GT -> let (Term vs' coef') = antiDTerm n (Term vs coef) in Term (v:vs') coef'

-- this does not add the constant to the antiderivative...
-- is mkC needed or is antiD an increasing map?
antiD :: Fin n -> C n -> C n
antiD n = mkC . fmap (antiDTerm n) . cTerms

gradient :: SNatI n => C n -> Vec n (C n)
gradient c = fmap (partialD c) V.universe

gradientAt :: SNatI n => Vec n Number -> C n -> Vec n Number
gradientAt vn = fmap (evalC vn) . gradient

nthPower :: Nat -> C n -> C n
nthPower Z     _ = sempty
nthPower (S n) t = sappend t $ nthPower n t


-- these are currently unused, but provide a way of
-- recursively evaluating C n, by evaluating x_0
-- and decreasing the dimension of all other variables
evalSpecificVar' :: Number -> Var (S n) -> Term n -> Term n
evalSpecificVar' _ _ ZeroTerm    = ZeroTerm
evalSpecificVar' n v (Term vs d) = case F.isMin (varDim v) of
  Nothing   -> Term vs $ d * (n ^ toNatural (S . varExp $ v))
  (Just v') -> Term (Var v' (varExp v):vs) d

partialEvalTerm' :: Number -> Term (S n) -> Term n
partialEvalTerm' _ ZeroTerm    = ZeroTerm
partialEvalTerm' n (Term vs d) = foldr (evalSpecificVar' n) (Term [] d) vs

partialEvalC' :: Number -> C (S n) -> C n
partialEvalC' n = mkC . fmap (partialEvalTerm' n) . cTerms

