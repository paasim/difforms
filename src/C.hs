{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module C where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), SNatI, toNatural )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import qualified Data.List as L
import Data.Maybe ( fromMaybe )
import Test.QuickCheck
import Common
import R

-- A variable x_i in n dimensions where
-- i < n
-- varExp i means x^(i+1) to disallow zero-powers
data Var n = Var { varDim :: Fin n, varExp :: Nat } deriving (Eq, Ord)

instance Show (Var n) where
  show (Var n Z)    = "x_" <> show n
  show (Var n exp)  = "x_" <> show n <> "^" <> show (S exp)

instance SNatI n => Arbitrary (Var n) where
  arbitrary = Var <$> (elements . V.toList $ V.universe)
                  <*> resize 4 arbitrary

evalVar :: R n -> Var n -> Number
evalVar r (Var ind exp) = (x r V.! ind) ^ (toNatural $ S exp)

-- for constructing valid instances of Term
varDimEq :: Var n -> Var n -> Bool
varDimEq v1 v2 = varDim v1 == varDim v2

-- only sensible when n1 == n2
-- +1 is because of the shifted representation for the exponents
varProd :: Var n -> Var n -> Var n
varProd (Var n1 exp1) (Var _ exp2) = Var n1 $ S exp1 + exp2


-- A product of variables with a coefficient
data Term n = ZeroTerm | Term [Var n] Number deriving (Eq, Ord)

instance Show (Term n) where
  show ZeroTerm    = show 0
  show (Term [] d) = show d
  show (Term vs d) = "(" <> show d <> ")*" <> (L.intercalate "*" . fmap show $ vs)

-- the monoid action on term(s) is multiplication, not sum
instance Semigroup (Term n) where
  ZeroTerm <> _ = ZeroTerm
  _ <> ZeroTerm = ZeroTerm
  (Term [] d) <> (Term vs' d') = Term vs'  $ d*d'
  (Term vs d) <> (Term []  d') = Term vs   $ d*d'
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
mkTerm vs d = Term (combineSimilar varDimEq varProd . L.sort $ vs) d where

evalTerm :: R n -> Term n -> Number
evalTerm _ ZeroTerm        = 0
evalTerm _ (Term [] d)     = d
evalTerm r (Term (v:vs) d) = evalVar r v * evalTerm r (Term vs d)

-- needed to make terms group
negateTerm :: Term n -> Term n
negateTerm ZeroTerm    = ZeroTerm
negateTerm (Term vs d) = Term vs (negate d)

-- for constructing valid instances of C
termVarsEq :: Term n -> Term n -> Bool
termVarsEq t1 t2 = vs t1 == vs t2 where
  vs ZeroTerm    = Nothing
  vs (Term vs _) = Just vs

-- only sensible when vars are equal
-- Does not take into account that d+d' might be zero,
-- this needs to be checked in the end
termSum :: Term n -> Term n -> Term n
termSum ZeroTerm    t           = t
termSum t           ZeroTerm    = t
termSum (Term vs d) (Term _ d') = if d + d' == 0
  then ZeroTerm
  else Term vs $ d + d'


-- A sum of nonzero term(s), ie. polynomials as terms is of the form
-- a*x_i*...*x_j + bx_h*...*x_k + ...
data C n = Terms (Term n) [Term n] deriving (Eq, Ord)

instance Show (C n) where
  show (Terms t [])       = "C: " <> show t
  show (Terms t1 (t2:ts)) = "C: " <> show t1 <> " + " <> (L.intercalate " + " . fmap show $ t2:ts)

instance SNatI n => Arbitrary (C n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkC <$> arbitrary <*> resize 4 arbitrary

-- the monoid action is now sum, not product as with term
-- (this is because terms needs to be a semiring)
instance Semigroup (C n) where
  (Terms t ts) <> (Terms t' ts') = (\(t'' :| ts'') -> Terms t'' ts'')
                                 . fromEmpty ZeroTerm
                                 . filter (ZeroTerm /=)
                                 . combineSimilar termVarsEq termSum
                                 $ merge (t:ts) (t':ts')

instance Monoid (C n) where
  mempty = liftToC ZeroTerm

-- Being (Abelian) Group and Semiring makes it a Ring
instance Group (C n) where
  ginv (Terms t ts) = Terms (negateTerm t) (fmap negateTerm ts)

-- this is the multiplication, kind of confusingly corresponding
-- to monoid action of term
instance Semirng (C n) where
  -- could use mempty term here but this is easier to read
  sappend (Terms t1 t1s) (Terms t2 t2s) =
    let (t :| ts) = (<>) <$> t1 :| t1s <*> t2 :| t2s in mkC t ts

instance Semiring (C n) where
  sempty = liftToC . liftToTerm $ 1

instance Algebra (C n) where
  amult a = sappend (liftToC . liftToTerm $ a)

liftToC :: Term n -> C n
liftToC t1 = Terms t1 []

-- A 'smart constructor' which ensures that the term(s)
-- are in correct order, terms with common variable-part are
-- summed together and and terms with coefficient 0 are filtered out
mkC :: Term n -> [Term n] -> C n
mkC t ts = (\(t :| ts) -> Terms t ts)
         . fromEmpty ZeroTerm
         . filter (ZeroTerm /=)
         . combineSimilar termVarsEq termSum
         $ L.sort (t:ts)

evalC :: R n -> C n -> Number
evalC r (Terms t1 [])      = evalTerm r t1
evalC r (Terms t1 (t2:ts)) = evalTerm r t1 + evalC r (Terms t2 ts)

-- not endomap due to term not containing sums
partialDTerm :: Term n -> Fin n -> C n
partialDTerm ZeroTerm n = liftToC ZeroTerm
partialDTerm (Term [] _) n = liftToC ZeroTerm
partialDTerm (Term (Var ind exp : vs) d) n =
  let f = liftToC $ Term [Var ind exp] 1
      g = liftToC $ Term vs d
      df = case (n == ind, exp) of
        (False, _)    -> liftToC ZeroTerm
        (True, Z)     -> liftToC . liftToTerm $ 1
        -- exp+1 because exp is one lower than the exponent
        (True, (S exp')) -> liftToC . Term [Var ind exp'] $ fromIntegral (S (S exp'))
      dg = partialDTerm (Term vs d) n
  -- f, g, df are Term, dg is a C
  in sappend df g <> sappend f dg

-- these form a basis on the tangent space
-- (this is :: Fin n -> V n)
partialD :: C n -> Fin n -> C n
partialD (Terms t1 [])      n = partialDTerm t1 n
partialD (Terms t1 (t2:ts)) n = partialDTerm t1 n <> partialD (Terms t2 ts) n

gradient :: SNatI n => C n -> Vec n (C n)
gradient c = fmap (partialD c) V.universe

gradientAt :: SNatI n => R n -> C n -> R n
gradientAt rn = R . fmap (evalC rn) . gradient

nthPower :: Nat -> C n -> C n
nthPower Z     _ = sempty
nthPower (S n) t = sappend t $ nthPower n t

