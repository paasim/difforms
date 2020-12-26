{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module OmegaP where

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
import Omega


-- ZeroCotermP corresponds to the case where C n is mempty
data CotermP p n = ZeroCotermP | CotermP (Vec p (Covar n)) (C n) deriving (Eq, Ord)

instance Show (CotermP p n) where
  show ZeroCotermP = show (mempty :: C n)
  show (CotermP VNil c) =
    "(" <> show c <> ")"
  show (CotermP cvs c) =
    "(" <> show c <> ")*" <> (L.intercalate "*" . fmap show  . V.toList $ cvs)

-- "semigroupoid" multiplication
cotermPMappend :: CotermP p1 n -> CotermP p2 n -> CotermP (Plus p1 p2) n
cotermPMappend ZeroCotermP _ = ZeroCotermP
cotermPMappend _ ZeroCotermP = ZeroCotermP
cotermPMappend (CotermP cvs c) (CotermP cvs' c') = mkCotermP (cvs V.++ cvs') $ sappend c c'

-- multiplicative identity
cotermPMempty :: CotermP Z n
cotermPMempty = liftToCotermP sempty

-- module multiplication (though group missing)
ctpMult :: C n -> CotermP p n -> CotermP p n
ctpMult _  ZeroCotermP     = ZeroCotermP
ctpMult c' (CotermP cvs c) = mkCotermP cvs $ sappend c' c

instance (SNatI p, SNatI n) => Arbitrary (CotermP p n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkCotermP <$> resize 2 arbitrary <*> arbitrary

liftToCotermP :: C n -> CotermP Z n
liftToCotermP = CotermP VNil

mkCotermP :: Vec p (Covar n) -> C n -> CotermP p n
mkCotermP cvs c = let (isEven, cvs') = bubbleVec cvs
  in case (c == mempty || not (uniqSortedVec cvs'), isEven) of
    (True,  _) -> ZeroCotermP
    (_,  True) -> CotermP cvs' c
    (_, False) -> negateCotermP $ CotermP cvs' c

evalCotermP :: Vec p (V n) -> CotermP p n -> C n
evalCotermP vs ZeroCotermP = mempty
evalCotermP vs (CotermP cvs c) = sappend c . foldr sappend sempty
  $ V.zipWith evalCovar vs cvs

negateCotermP :: CotermP p n -> CotermP p n
negateCotermP ZeroCotermP     = ZeroCotermP
negateCotermP (CotermP cvs c) = CotermP cvs $ ginv c

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


data OmegaP p n = CotermPs (CotermP p n) [CotermP p n]

instance Show (OmegaP p n) where
  show (CotermPs ctp ctps) = (<>) "OmegaP:\n  " . L.intercalate "\n + " . fmap show $ ctp:ctps

instance Semigroup (OmegaP p n) where
  (CotermPs ctp ctps) <> (CotermPs ctp' ctps') = mkOmegaP ctp $ ctps <> (ctp':ctps')

instance Monoid (OmegaP p n) where
  mempty = CotermPs ZeroCotermP []

instance Group (OmegaP p n) where
  ginv (CotermPs ctp ctps) = mkOmegaP (negateCotermP ctp) $ fmap negateCotermP ctps

instance Module (OmegaP p n) (C n) where
  mmult c (CotermPs ctp ctps) = mkOmegaP (ctpMult c ctp) $ fmap (ctpMult c) ctps

instance (SNatI p, SNatI n) => Arbitrary (OmegaP p n) where
  arbitrary = mkOmegaP <$> arbitrary <*> resize 4 (listOf arbitrary)

liftToOmegaP :: CotermP p n -> OmegaP p n
liftToOmegaP ctp = mkOmegaP ctp []

evalOmegaP :: Vec p (V n) -> OmegaP p n -> C n
evalOmegaP vs (CotermPs ctp ctps) =
  foldr (<>) (evalCotermP vs ctp) . fmap (evalCotermP vs) $ ctps

mkOmegaP :: CotermP p n -> [CotermP p n] -> OmegaP p n
-- filter twice so that sumSimilarTerms does not have to consider ZeroCotermP
mkOmegaP ctp = neToOmegaP . filterZeros . sumSimilarTerms . filterZeros . NE.sort . (:|) ctp where
  sumSimilarTerms :: NonEmpty (CotermP p n) -> NonEmpty (CotermP p n)
  sumSimilarTerms (ct :| [])       = ct :| []
  -- this is needed becasuse mkCotermP can make a term Zero
  sumSimilarTerms (ZeroCotermP :| CotermP cvs' c' : cts) =
    sumSimilarTerms (CotermP cvs' c' :| cts)
  sumSimilarTerms (CotermP cvs c :| CotermP cvs' c' : cts) = if cvs == cvs'
    then sumSimilarTerms $ mkCotermP cvs (c <> c') :| cts
    else CotermP cvs c <| sumSimilarTerms (CotermP cvs' c' :| cts)
  filterZeros :: NonEmpty (CotermP p n) -> NonEmpty (CotermP p n)
  filterZeros = fromMaybe (ZeroCotermP :| []) . NE.nonEmpty . NE.filter (ZeroCotermP /=)
  neToOmegaP (ctp :| ctps) = CotermPs ctp ctps

extProdCotermP :: OmegaP p2 n -> CotermP p1 n -> OmegaP (Plus p1 p2) n
extProdCotermP (CotermPs ctp ctps) ctp' =
  mkOmegaP (cotermPMappend ctp' ctp) $ fmap (cotermPMappend ctp') ctps

exteriorProductP :: OmegaP p1 n -> OmegaP p2 n -> OmegaP (Plus p1 p2) n
exteriorProductP (CotermPs ctp ctps) op =
  foldr (<>) (extProdCotermP op ctp) . fmap (extProdCotermP op) $ ctps

dCotermPBy :: CotermP p n -> Covar n -> CotermP (S p) n
dCotermPBy ZeroCotermP     _ = ZeroCotermP
dCotermPBy (CotermP cvs c) cv = mkCotermP (cv ::: cvs) (partialD c . covarDim $ cv)

dCotermP :: SNatI n => CotermP p n -> OmegaP (S p) n
dCotermP ctp = foldr (<>) mempty . fmap (liftToOmegaP . dCotermPBy ctp . Covar) $ V.universe

dP :: SNatI n => OmegaP p n -> OmegaP (S p) n
dP (CotermPs ctp ctps) = foldr (<>) (dCotermP ctp) $ fmap dCotermP ctps

d0P :: SNatI n => C n -> OmegaP (S Z) n
d0P = dP . liftToOmegaP . liftToCotermP

-- conversions between CotermP and Coterm and Omegap and Omega
cotermPToCoterm :: CotermP p n -> Coterm n
cotermPToCoterm ZeroCotermP = mkCoterm [] mempty
cotermPToCoterm (CotermP cvs c) = mkCoterm (V.toList cvs) c

cotermToCotermP :: SNatI p => Coterm n -> CotermP p n
cotermToCotermP (Coterm cvs c) = case V.fromList cvs of
  (Just cvs') -> mkCotermP cvs' c
  Nothing     -> ZeroCotermP

omegaPToOmega :: OmegaP p n -> Omega n
omegaPToOmega (CotermPs ctp ctps) = mkOmega (cotermPToCoterm ctp) $ fmap cotermPToCoterm ctps

omegaToOmegaP :: SNatI p => Omega n -> OmegaP p n
omegaToOmegaP (Coterms ct cts) = mkOmegaP (cotermToCotermP ct) $ fmap cotermToCotermP cts

