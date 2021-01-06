{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module D where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), Plus, SNatI )
import Data.Vec.Lazy ( Vec(..) )
import Data.Type.Nat.LE ( LE(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import Data.Maybe ( fromMaybe )
import Test.QuickCheck
import Typeclasses
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
  arbitrary = mkCoterm <$> resize 2 arbitrary <*> arbitrary

liftToCoterm :: C n -> Coterm Z n
liftToCoterm = Coterm VNil

mkCoterm :: Vec p (Covar n) -> C n -> Coterm p n
mkCoterm cvs c = let (isEven, cvs') = bubbleVec cvs
  in case (c == mempty || not (uniqSortedVec cvs'), isEven) of
    (True,  _) -> ZeroCoterm
    (_,  True) -> Coterm cvs' c
    (_, False) -> negateCoterm $ Coterm cvs' c

evalCoterm :: Vec p (V n) -> Coterm p n -> C n
evalCoterm vs ZeroCoterm = mempty
evalCoterm vs (Coterm cvs c) = sappend c . foldr sappend sempty
  $ V.zipWith evalCovar vs cvs

negateCoterm :: Coterm p n -> Coterm p n
negateCoterm ZeroCoterm     = ZeroCoterm
negateCoterm (Coterm cvs c) = Coterm cvs $ ginv c

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

uniqSortedVec :: Eq a => Vec n a -> Bool
uniqSortedVec VNil                 = True
uniqSortedVec (a ::: VNil)         = True
uniqSortedVec (a1 ::: a2 ::: rest) = a1 /= a2 && uniqSortedVec (a2 ::: rest)


data D p n = Coterms (Coterm p n) [Coterm p n]

instance Show (D p n) where
  show (Coterms ctp ctps) = (<>) "D:\n  " . L.intercalate "\n + " . fmap show $ ctp:ctps

instance Semigroup (D p n) where
  (Coterms ctp ctps) <> (Coterms ctp' ctps') = mkD ctp $ ctps <> (ctp':ctps')

instance Monoid (D p n) where
  mempty = Coterms ZeroCoterm []

instance Group (D p n) where
  ginv (Coterms ctp ctps) = mkD (negateCoterm ctp) $ fmap negateCoterm ctps

instance Module (D p n) (C n) where
  mmult c (Coterms ctp ctps) = mkD (ctpMult c ctp) $ fmap (ctpMult c) ctps

instance (SNatI p, SNatI n) => Arbitrary (D p n) where
  arbitrary = mkD <$> arbitrary <*> resize 4 (listOf arbitrary)

liftToD :: Coterm p n -> D p n
liftToD ctp = mkD ctp []

evalD :: Vec p (V n) -> D p n -> C n
evalD vs (Coterms ctp ctps) =
  foldr (<>) (evalCoterm vs ctp) . fmap (evalCoterm vs) $ ctps

mkD :: Coterm p n -> [Coterm p n] -> D p n
-- filter twice so that sumSimilarTerms does not have to consider ZeroCoterm
mkD ctp = neToD . filterZeros . sumSimilarTerms . filterZeros . NE.sort . (:|) ctp where
  sumSimilarTerms :: NonEmpty (Coterm p n) -> NonEmpty (Coterm p n)
  sumSimilarTerms (ct :| [])       = ct :| []
  -- this is needed becasuse mkCoterm can make a term Zero
  sumSimilarTerms (ZeroCoterm :| Coterm cvs' c' : cts) =
    sumSimilarTerms (Coterm cvs' c' :| cts)
  sumSimilarTerms (Coterm cvs c :| Coterm cvs' c' : cts) = if cvs == cvs'
    then sumSimilarTerms $ mkCoterm cvs (c <> c') :| cts
    else Coterm cvs c <| sumSimilarTerms (Coterm cvs' c' :| cts)
  filterZeros :: NonEmpty (Coterm p n) -> NonEmpty (Coterm p n)
  filterZeros = fromMaybe (ZeroCoterm :| []) . NE.nonEmpty . NE.filter (ZeroCoterm /=)
  neToD (ctp :| ctps) = Coterms ctp ctps

extProdCoterm :: D p2 n -> Coterm p1 n -> D (Plus p1 p2) n
extProdCoterm (Coterms ctp ctps) ctp' =
  mkD (cotermMappend ctp' ctp) $ fmap (cotermMappend ctp') ctps

exteriorProduct :: D p1 n -> D p2 n -> D (Plus p1 p2) n
exteriorProduct (Coterms ctp ctps) d =
  foldr (<>) (extProdCoterm d ctp) . fmap (extProdCoterm d) $ ctps

dCotermBy :: Coterm p n -> Covar n -> Coterm (S p) n
dCotermBy ZeroCoterm     _ = ZeroCoterm
dCotermBy (Coterm cvs c) cv = mkCoterm (cv ::: cvs) (partialD c . covarDim $ cv)

dCoterm :: SNatI n => Coterm p n -> D (S p) n
dCoterm ctp = foldr (<>) mempty . fmap (liftToD . dCotermBy ctp . Covar) $ V.universe

d :: SNatI n => D p n -> D (S p) n
d (Coterms ctp ctps) = foldr (<>) (dCoterm ctp) $ fmap dCoterm ctps

d0 :: SNatI n => C n -> D (S Z) n
d0 = d . liftToD . liftToCoterm

