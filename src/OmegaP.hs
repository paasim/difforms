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

mkCotermP :: Vec p (Covar n) -> C n -> CotermP p n
mkCotermP cvs c = if c == mempty then ZeroCotermP else CotermP cvs c

-- inserts an element and returns the position, Nothing if the element already exists
insertUniqueOrdered :: Ord a => a -> Vec n a -> Maybe (Int, Vec (S n) a)
insertUniqueOrdered a VNil = Just (0, a ::: VNil)
insertUniqueOrdered a (a' ::: rest) = case compare a a' of
  LT -> Just (0, a ::: a' ::: rest)
  EQ -> Nothing
  GT -> fmap (\(n, rest') -> (n+1, a ::: rest')) $ insertUniqueOrdered a rest

-- This is multiplication-like in the sense that appending to zero is zero
prependCovarP :: Covar n -> CotermP p n -> CotermP (S p) n
prependCovarP _ ZeroCotermP = ZeroCotermP
prependCovarP cv (CotermP cvs c) = case insertUniqueOrdered cv cvs of
  Nothing -> ZeroCotermP
  (Just (ind, cvs')) -> let len = V.length cvs'
                            c' = if mod ind 2 == 0 then c else ginv c
                        in CotermP cvs' c'

-- module multiplication
ctpMult :: C n -> CotermP p n -> CotermP p n
ctpMult c' (CotermP cvs c) = mkCotermP cvs $ sappend c' c

-- prepending works in incorrect order so the vec needs to be reversed
multCotermP' :: CotermP p1 n -> CotermP p2 n -> CotermP (N.Plus p1 p2) n
multCotermP' ZeroCotermP _ = ZeroCotermP
multCotermP' _ ZeroCotermP = ZeroCotermP
multCotermP' (CotermP VNil       c) ctp = ctpMult c ctp
multCotermP' (CotermP (cv:::cvs) c) ctp = prependCovarP cv $ multCotermP' (CotermP cvs c) ctp

-- "semigroupoid" multiplication
cotermPMappend :: CotermP p1 n -> CotermP p2 n -> CotermP (N.Plus p1 p2) n
cotermPMappend (CotermP cvs c) = multCotermP' (CotermP (V.reverse cvs) c)

-- multiplicative identity
cotermPMempty :: CotermP Z n
cotermPMempty = liftToCotermP sempty

liftToCotermP :: C n -> CotermP Z n
liftToCotermP = CotermP VNil

negateCotermP :: CotermP p n -> CotermP p n
negateCotermP (CotermP cvs c) = CotermP cvs $ ginv c

data OmegaP p n = CotermPs (CotermP p n) [CotermP p n] deriving Show

mkOmegaP :: CotermP p n -> [CotermP p n] -> OmegaP p n
-- filter twice so that sumSimilarTerms does not have to consider ZeroCotermP
mkOmegaP ctp = neToOmegaP . filterZeros . sumSimilarTerms . filterZeros . NE.sort . (:|) ctp where
  sumSimilarTerms :: NonEmpty (CotermP p n) -> NonEmpty (CotermP p n)
  sumSimilarTerms (ct :| [])       = ct :| []
  sumSimilarTerms (CotermP cvs c :| CotermP cvs' c' : cts) = if cvs == cvs'
    then sumSimilarTerms $ mkCotermP cvs (c <> c') :| cts
    else CotermP cvs c <| sumSimilarTerms (CotermP cvs' c' :| cts)
  -- remove all terms ZeroCotermP
  -- if the result is an empty list, keep one
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

exteriorProduct' :: OmegaP p n -> Omega n -> Omega n
exteriorProduct' op = exteriorProduct (omegaPToOmega op)

evalOmegaP :: Vec p (V n) -> OmegaP p n -> C n
evalOmegaP vs (CotermPs ctp ctps) = foldr (<>) mempty . fmap (evalCotermP vs) $ ctp:ctps

dCotermPBy :: CotermP p n -> Fin n -> CotermP (S p) n
dCotermPBy ctp n =
  let (CotermP cvs' c') = prependCovarP (Covar n) ctp
  in CotermP cvs' $ partialD c' n

dCotermP :: N.SNatI n => CotermP p n -> OmegaP (S p) n
dCotermP ctp = foldr (<>) mempty . fmap (liftToOmegaP . dCotermPBy ctp) $ V.universe

dp :: N.SNatI n => OmegaP p n -> OmegaP (S p) n
dp (CotermPs ctp ctps) = foldr (<>) (dCotermP ctp) $ fmap dCotermP ctps

d0 :: N.SNatI n => C n -> OmegaP (S Z) n
d0 = dp . liftToOmegaP . liftToCotermP

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

