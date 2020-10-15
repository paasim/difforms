{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module C where

import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import qualified Data.List as L
import Data.Function ( on )
import Data.Maybe ( fromMaybe )
import Test.QuickCheck
import Typeclasses
import R
import Phi

-- A variable x_i in n dimensions where
-- i < n
-- varExp i means x^(i+1) to disallow zero-powers
data Var n = Var { varDim :: Fin n, varExp :: Word } deriving (Eq, Ord)

instance Show (Var n) where
  show (Var n 0)    = "x_" <> show n
  show (Var n exp)  = "x_" <> show n <> "^" <> show (exp + 1)

evalVar :: Var n -> R n -> Double
evalVar (Var ind exp) r = (x r V.! ind) ^ (exp + 1)

instance N.SNatI n => Arbitrary (Var n) where
  arbitrary = Var <$> (elements . V.toList $ V.universe)
                  <*> elements [0..10]


-- A product of variables with a coefficient
data Term n = Term { termCoeff :: Double, termVars :: [Var n] }

liftToTerm :: Double -> Term n
liftToTerm a = Term a []

-- A 'smart constructor' that removes variables
-- when the coefficient is zero, combines variables
-- with same dimension and sorts the variables
-- in ascending order for simpler comparison and printing
mkTerm :: Double -> [Var n] -> Term n
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

evalTerm :: Term n -> R n -> Double
evalTerm (Term d [])     _ = d
evalTerm (Term d (v:vs)) r = evalVar v r * evalTerm (Term d vs) r

instance Show (Term n) where
  show (Term d []) = show d
  show (Term d l)  = show d <> "*" <> (L.intercalate "*" . fmap show $ l)

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

instance N.SNatI n => Arbitrary (Term n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkTerm <$> fmap fromInteger arbitrary <*> listOf arbitrary

-- the monoid action on term(s) is multiplication, not sum
instance Semigroup (Term n) where
  (Term 0 _) <> (Term _ _)   = liftToTerm 0
  (Term _ _) <> (Term 0 _)   = liftToTerm 0
  (Term d l) <> (Term d' l') = mkTerm (d*d') $ l <> l'

instance Monoid (Term n) where
  mempty = liftToTerm 1

-- A sum of nonzero term(s), ie. polynomials as terms is of the form
-- a*x_i*...*x_j + bx_h*...*x_k + ...
newtype Terms n = Terms (NonEmpty (Term n)) deriving (Eq, Ord)

liftToTerms :: Term n -> Terms n
liftToTerms t1 = Terms $ t1 :| []

-- A 'smart constructor' which ensures that the term(s)
-- are in correct order, terms with common variable-part are
-- summed together and and terms with coefficient 0 are filtered out
mkTerms :: Term n -> [Term n] -> Terms n
mkTerms t ts = Terms . filterZeros . sumSimilarTerms . NE.sort $ t :| ts where
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

evalTerms :: Terms n -> R n -> Double
evalTerms (Terms (t1 :| []))    r = evalTerm t1 r
evalTerms (Terms (t1 :| t2:ts)) r = evalTerm t1 r * evalTerms (Terms $ t2 :| ts) r

instance Show (Terms n) where
  show (Terms (t :| []))   = show t
  show (Terms (t :| rest)) = show t <> " + " <> (L.intercalate " + " . fmap show $ rest)

instance N.SNatI n => Arbitrary (Terms n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkTerms <$> arbitrary <*> listOf arbitrary

-- the monoid action is now sum, not product as with term
-- (this is because terms needs to be a semiring)
instance Semigroup (Terms n) where
  (Terms ts1) <> (Terms ts2) = let (t :| ts) = ts1 <> ts2 in mkTerms t ts

instance Monoid (Terms n) where
  mempty = liftToTerms . liftToTerm $ 0

-- this is the multiplication, kind of confusingly corresponding
-- to monoid action of term
instance Semirng (Terms n) where
  -- could use mempty term here but this is easier to read
  sappend (Terms ts1) (Terms ts2) = let (t :| ts) = ((<>) <$> ts1 <*> ts2) in mkTerms t ts

instance Semiring (Terms n) where
  sempty = liftToTerms . liftToTerm $ 1

nthPower :: Word -> Terms n -> Terms n
nthPower 0 _ = sempty
nthPower n t = sappend t $ nthPower (n-1) t

instance Algebra (Terms n) where
  amult a = sappend (liftToTerms . liftToTerm $ a)

-- not endomap due to term not containing sums
partialDTerm :: Fin n -> Term n -> Terms n
partialDTerm _ (Term _ []) = liftToTerms . liftToTerm $ 0
partialDTerm n (Term d (Var ind exp : rest)) =
  let f = liftToTerms $ Term 1 [Var ind exp]
      g = liftToTerms $ Term d rest
      df = case (n == ind, exp == 0) of
        (False, _)   -> liftToTerms . liftToTerm $ 0
        (True, True) -> liftToTerms . liftToTerm $ 1
        -- exp+1 because exp is one lower than the exponent
        (True, False) -> liftToTerms . Term (fromIntegral exp + 1) $ [Var ind (exp-1)]
      dg = partialDTerm n (Term d rest)
  -- f, g, df are Term, dg is a Terms
  in sappend df g <> sappend f dg

-- these form a basis on the tangent space
-- (this is :: Fin n -> V n)
partialD :: Fin n -> Terms n -> Terms n
partialD n (Terms (t1 :| []))    = partialDTerm n t1
partialD n (Terms (t1 :| t2:ts)) = partialDTerm n t1 <> partialD n (Terms (t2 :| ts))

-- given coefficients, uses the basis
-- (this is :: R n -> V n)
-- this is just a different representation for V.evalV
tangent :: N.SNatI n => R n -> Terms n -> Terms n
tangent v ts = foldr (<>) mempty . V.zipWith amult (x v) . fmap (\n -> partialD n ts) $ V.universe

-- not endomap due to term not containing sums
pullbackTerm :: N.SNatI m => Phi' n m -> Term m -> Terms n
pullbackTerm _   (Term d [])             = liftToTerms . liftToTerm $ d
pullbackTerm phi (Term d (Var ind exp : ts)) =
  -- given coefficient d' and index i, constructs a term
  let termWithCoef i d' = liftToTerms $ Term d' [Var i 0]
  -- construct the sum of terms given a cofficient vector (of type R n)
      sumTerms = V.ifoldr (\i d' -> (<>) (termWithCoef i d')) mempty . x
  -- picks the correct vector from phi and multiplies with the other terms recursively
  in sappend (nthPower (exp+1) . sumTerms $ mat (transpose phi) V.! ind)
             (pullbackTerm phi $ Term d ts)

-- precomposes f with the manifold map
pullback :: N.SNatI m => Phi' n m -> Terms m -> Terms n
pullback phi (Terms (t1 :| []))    = pullbackTerm phi t1
pullback phi (Terms (t1 :| t2:ts)) = pullbackTerm phi t1 <> pullback phi (Terms (t2 :| ts))

-- C n, the set of continuous functions is approximated by polynomials
type C' n = Terms n

-- this is what I would like to get
--newtype C n = C { runC :: R n -> Double }

--pullbackC :: Phi n m -> C m -> C n
--pullbackC (Phi nToM) (C mToD) = C $ mToD . nToM

