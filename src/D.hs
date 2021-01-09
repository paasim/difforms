{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module D where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), Plus, SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Test.QuickCheck
import Common
import R
import C
import V

-- dx, dy etc
newtype Covar n = Covar { covarDim :: Fin n } deriving (Eq, Ord)

instance Show (Covar n) where
  show (Covar n)    = "dx_" <> show n

instance SNatI n => Arbitrary (Covar n) where
  arbitrary = Covar <$> (elements . V.toList $ V.universe)

evalCovar :: V n -> Covar n -> C n
evalCovar v (Covar n) = vComp v V.! n

-- ZeroCoterm corresponds to the case where C n is mempty
data Coterm p n = ZeroCoterm | Coterm (Vec p (Covar n)) (C n) deriving (Eq, Ord)

instance Show (Coterm p n) where
  show ZeroCoterm = show (mempty :: C n)
  show (Coterm VNil c) =
    "(" <> show c <> ")"
  show (Coterm cvs c) =
    "(" <> show c <> ")*" <> (L.intercalate "*" . fmap show  . V.toList $ cvs)

-- "semigroupoid" multiplication
cotermMappend :: Coterm p1 n -> Coterm p2 n -> Coterm (Plus p1 p2) n
cotermMappend ZeroCoterm _ = ZeroCoterm
cotermMappend _ ZeroCoterm = ZeroCoterm
cotermMappend (Coterm cvs c) (Coterm cvs' c') = mkCoterm (cvs V.++ cvs') $ sappend c c'

-- multiplicative identity
cotermMempty :: Coterm Z n
cotermMempty = liftToCoterm sempty

-- module multiplication (though group missing)
ctpMult :: C n -> Coterm p n -> Coterm p n
ctpMult _  ZeroCoterm     = ZeroCoterm
ctpMult c' (Coterm cvs c) = mkCoterm cvs $ sappend c' c

instance (SNatI p, SNatI n) => Arbitrary (Coterm p n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkCoterm <$> arbitrary <*> arbitrary

liftToCoterm :: C n -> Coterm Z n
liftToCoterm = Coterm VNil

mkCoterm :: Vec p (Covar n) -> C n -> Coterm p n
mkCoterm cvs c = let (isEven, cvs') = bubbleVec cvs
  in case (c == mempty || not (uniqSortedVec cvs'), isEven) of
    (True,  _) -> ZeroCoterm --coef is zero or two coterms of same dimension
    (_,  True) -> Coterm cvs' c
    (_, False) -> negateCoterm $ Coterm cvs' c -- negate because of anticommutativity

evalCoterm :: Vec p (V n) -> Coterm p n -> C n
evalCoterm vs ZeroCoterm = mempty
evalCoterm vs (Coterm cvs c) = sappend c . foldr sappend sempty
  $ V.zipWith evalCovar vs cvs

negateCoterm :: Coterm p n -> Coterm p n
negateCoterm ZeroCoterm     = ZeroCoterm
negateCoterm (Coterm cvs c) = Coterm cvs $ ginv c

-- keeps track of the permutation (even or odd)
insertVec :: Ord a => a -> Bool -> Vec n a -> (Bool, Vec (S n) a)
insertVec a b VNil = (b, a ::: VNil)
insertVec a b (a' ::: rest) = if a < a'
  then (b, a ::: a' ::: rest)
  else (a' :::) <$> insertVec a (not b) rest

-- bubblesort, but keeps track of whether the
-- sorted list is an even permutation
bubbleVec :: Ord a => Vec n a -> (Bool, Vec n a)
bubbleVec VNil = (True, VNil)
bubbleVec (a ::: as) = uncurry (insertVec a) $ bubbleVec as

-- check whether all the elements are unique,
-- assumes that the vec is sorted
uniqSortedVec :: Eq a => Vec n a -> Bool
uniqSortedVec VNil                 = True
uniqSortedVec (a ::: VNil)         = True
uniqSortedVec (a1 ::: a2 ::: rest) = a1 /= a2 && uniqSortedVec (a2 ::: rest)


-- for constructing valid instances of D
cotermVarsEq :: Coterm p n -> Coterm p n -> Bool
cotermVarsEq ct1 ct2 = cvs ct1 == cvs ct2 where
  cvs ZeroCoterm     = Nothing
  cvs (Coterm cvs _) = Just cvs

-- Sum of two terms assuming the vars are equal
cotermSum :: Coterm p n -> Coterm p n -> Coterm p n
cotermSum ct             ZeroCoterm    = ct
cotermSum ZeroCoterm     ct            = ct
cotermSum (Coterm cvs c) (Coterm _ c') =
  if c <> c' == mempty then ZeroCoterm else Coterm cvs $ c <> c'


-- A differential form represented as a sum of nonzero coterm(s),
-- ie. differential forms such as, f(x1,x2,x3)dx_1dx_2 + g(x1,x2,x3)dx_2dx_3
-- where f,g are of type C 3
data D p n = Coterms (Coterm p n) [Coterm p n]

instance Show (D p n) where
  show (Coterms ctp ctps) = (<>) "D:\n  " . L.intercalate "\n + " . fmap show $ ctp:ctps

instance Semigroup (D p n) where
  (Coterms ct cts) <> (Coterms ct' cts') =
    fromEmpty Coterms ZeroCoterm -- if the result is an empty list, take a ZeroCoterm
    . filter (ZeroCoterm /=) -- Remove 0s from the sum
    . combineSimilar cotermVarsEq cotermSum -- adx_1dx_2 + bdx_1dx_2 = (a+b)dx_1dx_2 etc.
    $ merge (ct:cts) (ct':cts') --these are already ordered so a merge is enough

instance Monoid (D p n) where
  mempty = Coterms ZeroCoterm []

instance Group (D p n) where
  ginv (Coterms ctp ctps) = mkD (negateCoterm ctp) $ fmap negateCoterm ctps

instance Module (D p n) (C n) where
  mmult c (Coterms ctp ctps) = mkD (ctpMult c ctp) $ fmap (ctpMult c) ctps

instance (SNatI p, SNatI n) => Arbitrary (D p n) where
  arbitrary = mkD <$> arbitrary <*> resize 4 arbitrary

liftToD :: Coterm p n -> D p n
liftToD ctp = mkD ctp []

evalD :: Vec p (V n) -> D p n -> C n
evalD vs (Coterms ctp ctps) =
  foldr (<>) (evalCoterm vs ctp) . fmap (evalCoterm vs) $ ctps

-- see comments for the semigroup instance, this is similar
-- but does not assume that the coterms are sorted
mkD :: Coterm p n -> [Coterm p n] -> D p n
mkD ct cts = fromEmpty Coterms ZeroCoterm
           . filter (ZeroCoterm /=)
           . combineSimilar cotermVarsEq cotermSum
           $ L.sort (ct:cts) where

-- cotermMappend is the product (2dx_3 * 3dx_1 = -6dx_1dx_3)
extProdCoterm :: D p2 n -> Coterm p1 n -> D (Plus p1 p2) n
extProdCoterm (Coterms ctp ctps) ctp' =
  mkD (cotermMappend ctp' ctp) $ fmap (cotermMappend ctp') ctps

-- fold over the coterms
exteriorProduct :: D p1 n -> D p2 n -> D (Plus p1 p2) n
exteriorProduct (Coterms ctp ctps) d =
  foldr (<>) (extProdCoterm d ctp) . fmap (extProdCoterm d) $ ctps

-- partial derivative with respect to a given dimension
dCotermBy :: Coterm p n -> Covar n -> Coterm (S p) n
dCotermBy ZeroCoterm     _ = ZeroCoterm
dCotermBy (Coterm cvs c) cv = mkCoterm (cv ::: cvs) (partialD c . covarDim $ cv)

-- fold over all the dimensions
dCoterm :: SNatI n => Coterm p n -> D (S p) n
dCoterm ctp = foldr (<>) mempty . fmap (liftToD . dCotermBy ctp . Covar) $ V.universe

-- foldr over coterms
d :: SNatI n => D p n -> D (S p) n
d (Coterms ctp ctps) = foldr (<>) (dCoterm ctp) $ fmap dCoterm ctps

-- same as d but for C n which are interpreted as 0-forms (D Z n)
d0 :: SNatI n => C n -> D (S Z) n
d0 = d . liftToD . liftToCoterm

