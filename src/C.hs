{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module C where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import qualified Data.List as L
import Data.Function ( on )
import Data.Maybe ( fromMaybe )
import Test.QuickCheck
import Typeclasses
import R

-- A variable x_i in n dimensions where
-- i < n
-- varExp i means x^(i+1) to disallow zero-powers
data Var n = Var { varDim :: Fin n, varExp :: Word } deriving (Eq, Ord)

instance Show (Var n) where
  show (Var n 0)    = "x_" <> show n
  show (Var n exp)  = "x_" <> show n <> "^" <> show (exp + 1)

instance SNatI n => Arbitrary (Var n) where
  arbitrary = Var <$> (elements . V.toList $ V.universe)
                  <*> elements [0..5]

evalVar :: R n -> Var n -> Rational
evalVar r (Var ind exp) = (x r V.! ind) ^ (exp + 1)


-- A product of variables with a coefficient
data Term n = Term { termCoeff :: Rational, termVars :: [Var n] }

instance Show (Term n) where
  show (Term d []) = show d
  show (Term d l)  = "(" <> show d <> ")*" <> (L.intercalate "*" . fmap show $ l)

instance Eq (Term n) where
  (Term 0 _) == (Term 0 _) = True
  (Term d l) == (Term d' l') = d == d' && ((==) `on` L.sort) l l'

instance Ord (Term n) where
  (Term 0 _) <= (Term 0 []) = True
  (Term 0 []) <= (Term 0 _) = True
  (Term d l) <= (Term d' l') = case (compare l l', d <= d') of
    (EQ, dComp) -> dComp
    (LT, _)     -> True
    (GT, _)     -> False

-- the monoid action on term(s) is multiplication, not sum
instance Semigroup (Term n) where
  (Term 0 _) <> (Term _ _)   = liftToTerm 0
  (Term _ _) <> (Term 0 _)   = liftToTerm 0
  (Term d l) <> (Term d' l') = mkTerm (d*d') $ l <> l'

instance Monoid (Term n) where
  mempty = liftToTerm 1

instance SNatI n => Arbitrary (Term n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkTerm <$> genSimpleRational <*> resize 2 (listOf arbitrary)

liftToTerm :: Rational -> Term n
liftToTerm a = Term a []

-- A 'smart constructor' that removes variables
-- when the coefficient is zero, combines variables
-- with same dimension and sorts the variables
-- in ascending order for simpler comparison and printing
mkTerm :: Rational -> [Var n] -> Term n
mkTerm 0 _ = liftToTerm 0
mkTerm d l = Term d . multiplySimilarTerms . L.sort $ l where
    -- [x, x, y] -> [x^2, y]
  multiplySimilarTerms :: [Var n] -> [Var n]
  multiplySimilarTerms []                                 = []
  multiplySimilarTerms [t]                                = [t]
  multiplySimilarTerms (Var n1 exp1 : Var n2 exp2 : rest) = if n1 == n2
    -- +1 is because of the shifted representation for the exponents
    then multiplySimilarTerms $ Var n1 (exp1+exp2+1) : rest
    else Var n1 exp1 : multiplySimilarTerms (Var n2 exp2 : rest)

evalTerm :: R n -> Term n -> Rational
evalTerm _ (Term d [])     = d
evalTerm r (Term d (v:vs)) = evalVar r v * evalTerm r (Term d vs)

-- needed to make terms group
negateTerm :: Term n -> Term n
negateTerm (Term d l) = Term (negate d) l


-- A sum of nonzero term(s), ie. polynomials as terms is of the form
-- a*x_i*...*x_j + bx_h*...*x_k + ...
newtype C n = Terms (NonEmpty (Term n)) deriving (Eq, Ord)

instance Show (C n) where
  show (Terms (t :| []))   = "C: " <> show t
  show (Terms (t :| rest)) = "C: " <> show t <> " + " <> (L.intercalate " + " . fmap show $ rest)

instance SNatI n => Arbitrary (C n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkC <$> arbitrary <*> resize 4 (listOf arbitrary)

-- the monoid action is now sum, not product as with term
-- (this is because terms needs to be a semiring)
instance Semigroup (C n) where
  (Terms c1) <> (Terms c2) = let (t :| ts) = c1 <> c2 in mkC t ts

instance Monoid (C n) where
  mempty = liftToC . liftToTerm $ 0

-- Being (Abelian) Group and Semiring makes it a Ring
instance Group (C n) where
  ginv (Terms (t :| ts)) = mkC (negateTerm t) (fmap negateTerm ts)

-- this is the multiplication, kind of confusingly corresponding
-- to monoid action of term
instance Semirng (C n) where
  -- could use mempty term here but this is easier to read
  sappend (Terms c1) (Terms c2) = let (t :| ts) = ((<>) <$> c1 <*> c2) in mkC t ts

instance Semiring (C n) where
  sempty = liftToC . liftToTerm $ 1

instance Algebra (C n) where
  amult a = sappend (liftToC . liftToTerm $ a)

liftToC :: Term n -> C n
liftToC t1 = Terms $ t1 :| []

-- A 'smart constructor' which ensures that the term(s)
-- are in correct order, terms with common variable-part are
-- summed together and and terms with coefficient 0 are filtered out
mkC :: Term n -> [Term n] -> C n
mkC t ts = Terms . filterZeros . sumSimilarTerms . NE.sort $ t :| ts where
  -- [2xy^2, -5xy^2, 3x] -> [-3xy^2, 3x]
  sumSimilarTerms :: NonEmpty (Term n) -> NonEmpty (Term n)
  sumSimilarTerms (t :| [])       = t :| []
  sumSimilarTerms (Term d l :| Term d' l' : ts) = if ((==) `on` L.sort) l l'
    then sumSimilarTerms $ Term (d+d') l :| ts
    else Term d l <| sumSimilarTerms (Term d' l' :| ts)
  -- remove all terms with 0 as coefficient but
  -- if the result is an empty list, keep one
  filterZeros :: NonEmpty (Term n) -> NonEmpty (Term n)
  filterZeros = fromMaybe (liftToTerm 0 :| []) . NE.nonEmpty . NE.filter (liftToTerm 0 /=)

evalC :: R n -> C n -> Rational
evalC r (Terms (t1 :| []))    = evalTerm r t1
evalC r (Terms (t1 :| t2:ts)) = evalTerm r t1 + evalC r (Terms $ t2 :| ts)

-- not endomap due to term not containing sums
partialDTerm :: Term n -> Fin n -> C n
partialDTerm (Term _ []) n = liftToC . liftToTerm $ 0
partialDTerm (Term d (Var ind exp : rest)) n =
  let f = liftToC $ Term 1 [Var ind exp]
      g = liftToC $ Term d rest
      df = case (n == ind, exp == 0) of
        (False, _)   -> liftToC . liftToTerm $ 0
        (True, True) -> liftToC . liftToTerm $ 1
        -- exp+1 because exp is one lower than the exponent
        (True, False) -> liftToC . Term (fromIntegral exp + 1) $ [Var ind (exp-1)]
      dg = partialDTerm (Term d rest) n
  -- f, g, df are Term, dg is a C
  in sappend df g <> sappend f dg

-- these form a basis on the tangent space
-- (this is :: Fin n -> V n)
partialD :: C n -> Fin n -> C n
partialD (Terms (t1 :| []))    n = partialDTerm t1 n
partialD (Terms (t1 :| t2:ts)) n = partialDTerm t1 n <> partialD (Terms (t2 :| ts)) n

gradient :: SNatI n => C n -> Vec n (C n)
gradient c = fmap (partialD c) V.universe

gradientAt :: SNatI n => R n -> C n -> R n
gradientAt rn = R . fmap (evalC rn) . gradient

nthPower :: Word -> C n -> C n
nthPower 0 _ = sempty
nthPower n t = sappend t $ nthPower (n-1) t

