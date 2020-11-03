{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module OmegaP where

import qualified Data.Map.Strict as M
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import qualified Data.Type.Nat as N
import qualified Data.List as L
import Data.List.NonEmpty ( NonEmpty(..), (<|) )
import qualified Data.List.NonEmpty as NE
import Data.Type.Nat.LE ( LE(..) )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Maybe ( fromMaybe )
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import Omega


-- ZeroCotermP corresponds to the case where C n is mempty
data CotermP p n = ZeroCotermP | CotermP (Vec p (Covar n)) (C n) deriving (Eq, Ord)

evalCotermP :: Vec p (V n) -> CotermP p n -> C n
evalCotermP vs ZeroCotermP = mempty
evalCotermP vs (CotermP cvs c) = sappend c . foldr sappend sempty
  $ V.zipWith evalCovar vs cvs

instance Show (CotermP p n) where
  show ZeroCotermP = show (mempty :: C n)
  show (CotermP VNil c) =
    "(" <> show c <> ")"
  show (CotermP cvs c) =
    "(" <> show c <> ")*" <> (L.intercalate "*" . fmap show  . V.toList $ cvs)

negateCotermP :: CotermP p n -> CotermP p n
negateCotermP ZeroCotermP     = ZeroCotermP
negateCotermP (CotermP cvs c) = CotermP cvs $ ginv c

insert' :: Ord a => a -> Bool -> Vec n a -> (Bool, Vec (S n) a)
insert' a b VNil = (b, a ::: VNil)
insert' a b (a' ::: rest) = if a < a'
  then (b, a ::: a' ::: rest)
  else fmap (a' :::) $ insert' a (not b) rest

bubble :: Ord a => Vec n a -> (Bool, Vec n a)
bubble VNil = (True, VNil)
bubble (a ::: as) = uncurry (insert' a) $ bubble as

uniqSorted :: Eq a => Vec n a -> Bool
uniqSorted VNil = True
uniqSorted (a ::: VNil) = True
uniqSorted (a1 ::: a2 ::: rest) = a1 /= a2 && uniqSorted (a2 ::: rest)

mkCotermP :: Vec p (Covar n) -> C n -> CotermP p n
mkCotermP cvs c = let (isEven, cvs') = bubble cvs
  in case (c == mempty || not (uniqSorted cvs'), isEven) of
    (True,  _) -> ZeroCotermP
    (_,  True) -> CotermP cvs' c
    (_, False) -> negateCotermP $ CotermP cvs' c

-- module multiplication
ctpMult :: C n -> CotermP p n -> CotermP p n
ctpMult _  ZeroCotermP     = ZeroCotermP
ctpMult c' (CotermP cvs c) = mkCotermP cvs $ sappend c' c

-- "semigroupoid" multiplication
cotermPMappend :: CotermP p1 n -> CotermP p2 n -> CotermP (N.Plus p1 p2) n
cotermPMappend ZeroCotermP _ = ZeroCotermP
cotermPMappend _ ZeroCotermP = ZeroCotermP
cotermPMappend (CotermP cvs c) (CotermP cvs' c') = mkCotermP (cvs V.++ cvs') $ sappend c c'

-- multiplicative identity
cotermPMempty :: CotermP Z n
cotermPMempty = liftToCotermP sempty

liftToCotermP :: C n -> CotermP Z n
liftToCotermP = CotermP VNil

instance (N.SNatI p, N.SNatI n) => Arbitrary (CotermP p n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkCotermP <$> resize 2 arbitrary <*> arbitrary


data OmegaP p n = CotermPs (CotermP p n) [CotermP p n] deriving Show

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

instance Semigroup (OmegaP p n) where
  (CotermPs ctp ctps) <> (CotermPs ctp' ctps') = mkOmegaP ctp $ ctps <> (ctp':ctps')

instance Monoid (OmegaP p n) where
  mempty = CotermPs ZeroCotermP []

instance Group (OmegaP p n) where
  ginv (CotermPs ctp ctps) = mkOmegaP (negateCotermP ctp) $ fmap negateCotermP ctps

instance Module (OmegaP p n) (C n) where
  mmult c (CotermPs ctp ctps) = mkOmegaP (ctpMult c ctp) $ fmap (ctpMult c) ctps

liftToOmegaP :: CotermP p n -> OmegaP p n
liftToOmegaP ctp = mkOmegaP ctp []

extProdCotermP :: CotermP p1 n -> OmegaP p2 n -> OmegaP (N.Plus p1 p2) n
extProdCotermP ctp' (CotermPs ctp ctps) =
  mkOmegaP (cotermPMappend ctp' ctp) $ fmap (cotermPMappend ctp') ctps

exteriorProductP :: OmegaP p1 n -> OmegaP p2 n -> OmegaP (N.Plus p1 p2) n
exteriorProductP (CotermPs ctp ctps) op =
  foldr (<>) (extProdCotermP ctp op) . fmap (\ctp -> extProdCotermP ctp op) $ ctps

evalOmegaP :: Vec p (V n) -> OmegaP p n -> C n
evalOmegaP vs (CotermPs ctp ctps) =
  foldr (<>) (evalCotermP vs ctp) . fmap (evalCotermP vs) $ ctps

--exteriorProduct' :: OmegaP p n -> Omega n -> Omega n
--exteriorProduct' op = exteriorProduct (omegaPToOmega op)

instance (N.SNatI p, N.SNatI n) => Arbitrary (OmegaP p n) where
  arbitrary = mkOmegaP <$> arbitrary <*> resize 4 (listOf arbitrary)

dCotermPBy :: CotermP p n -> Covar n -> CotermP (S p) n
dCotermPBy ZeroCotermP     _ = ZeroCotermP
dCotermPBy (CotermP cvs c) cv = mkCotermP (cv ::: cvs) (partialD c . covarDim $ cv)

dCotermP :: N.SNatI n => CotermP p n -> OmegaP (S p) n
dCotermP ctp = foldr (<>) mempty . fmap (liftToOmegaP . dCotermPBy ctp . Covar) $ V.universe

dP :: N.SNatI n => OmegaP p n -> OmegaP (S p) n
dP (CotermPs ctp ctps) = foldr (<>) (dCotermP ctp) $ fmap dCotermP ctps

d0 :: N.SNatI n => C n -> OmegaP (S Z) n
d0 = dP . liftToOmegaP . liftToCotermP

-- conversions between CotermP and Coterm and Omegap and Omega
cotermPToCoterm :: CotermP p n -> Coterm n
cotermPToCoterm ZeroCotermP = mkCoterm mempty []
cotermPToCoterm (CotermP cvs c) = mkCoterm c . V.toList $ cvs

cotermToCotermP :: N.SNatI p => Coterm n -> CotermP p n
cotermToCotermP (Coterm cvs c) = case V.fromList . S.toList $ cvs of
  (Just cvs') -> mkCotermP cvs' c
  Nothing     -> ZeroCotermP

omegaPToOmega :: OmegaP p n -> Omega n
omegaPToOmega (CotermPs ctp ctps) = mkOmega (cotermPToCoterm ctp) $ fmap cotermPToCoterm ctps

omegaToOmegaP :: N.SNatI p => Omega n -> OmegaP p n
omegaToOmegaP (Coterms ct cts) = mkOmegaP (cotermToCotermP ct) $ fmap cotermToCotermP cts

