{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Omega where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), SNatI )
import Data.Vec.Lazy ( Vec(..) )
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
  show (Covar n)    = "d_" <> show n

instance SNatI n => Arbitrary (Covar n) where
  arbitrary = Covar <$> (elements . V.toList $ V.universe)

evalCovar :: V n -> Covar n -> C n
evalCovar v (Covar n) = vComp v V.! n


-- (Exterior) products of covars with a C n coefficient
data Coterm n = Coterm { cotermVars :: [Covar n], cotermCoeff :: C n } deriving (Eq, Ord)

instance Show (Coterm n) where
  show (Coterm []  c) = show c
  show (Coterm cvs c) =
    "(" <> show c <> ")*" <> (L.intercalate "*" . fmap show $ cvs)

instance Semigroup (Coterm n) where
  (Coterm cvs c) <> (Coterm cvs' c') = mkCoterm (cvs <> cvs') $ c `sappend` c'

instance Monoid (Coterm n) where
  mempty = liftToCoterm mempty

-- module multiplication (though group missing)
ctMult :: C n -> Coterm n -> Coterm n
ctMult c' (Coterm cvs c) = mkCoterm cvs (sappend c c')

instance SNatI n => Arbitrary (Coterm n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkCoterm <$> resize 2 (listOf arbitrary)
                       <*> arbitrary

liftToCoterm :: C n -> Coterm n
liftToCoterm c = Coterm [] c

mkCoterm :: [Covar n] -> C n -> Coterm n
--foldr prependCovar (liftToCoterm c)
mkCoterm cvs c = let (isEven, cvs') = bubbleList cvs
  in case (c == mempty || not (uniqSortedList cvs'), isEven) of
    (True,  _) -> mempty
    (_,  True) -> Coterm cvs' c
    (_, False) -> negateCoterm $ Coterm cvs' c

evalCoterm :: Vec n (V n) -> Coterm n -> C n
evalCoterm vs (Coterm cvs c') = sappend c' . foldr sappend sempty
  $ zipWith evalCovar (V.toList vs) cvs

negateCoterm :: Coterm n -> Coterm n
negateCoterm (Coterm cvs c) = Coterm cvs $ ginv c

insertList :: Ord a => a -> Bool -> [a] -> (Bool, [a])
insertList a' b []     = (b, [a'])
insertList a' b (a:as) = if a' < a
  then (b, a' : a : as)
  else fmap (a :) $ insertList a' (not b) as

bubbleList :: Ord a => [a] -> (Bool, [a])
bubbleList []       = (True, [])
bubbleList (a : as) = uncurry (insertList a) $ bubbleList as

uniqSortedList :: Eq a => [a] -> Bool
uniqSortedList []         = True
uniqSortedList [a]        = True
uniqSortedList (a1:a2:as) = a1 /= a2 && uniqSortedList (a2:as)

listMember :: Eq a => a -> [a] -> Bool
listMember a' [] = False
listMember a' (a:as) = a' == a || listMember a' as


-- n-forms from n-manifold, hopefully these could be refactored
-- into p-forms (where p<=n)
data Omega n = Coterms (Coterm n) [Coterm n]

instance Show (Omega n) where
  show (Coterms ct cts) = (<>) "Omega:\n  " . L.intercalate "\n + " . fmap show $ ct:cts

instance Semigroup (Omega n) where
  (Coterms c1 c1s) <> (Coterms c2 c2s) = mkOmega c1 $ c1s <> (c2 : c2s)

instance Monoid (Omega n) where
  mempty = liftToOmega . liftToCoterm $ mempty

-- Being (Abelian) Group and Semiring makes it a Ring
instance Group (Omega n) where
  ginv (Coterms ct cts) = mkOmega (negateCoterm ct) $ fmap negateCoterm cts

instance Module (Omega n) (C n) where
  mmult c (Coterms ct cts) = mkOmega (ctMult c ct) $ fmap (ctMult c) cts

instance SNatI n => Arbitrary (Omega n) where
  arbitrary = mkOmega <$> arbitrary <*> resize 4 (listOf arbitrary)

liftToOmega :: Coterm n -> Omega n
liftToOmega ct = mkOmega ct []

mkOmega :: Coterm n -> [Coterm n] -> Omega n
mkOmega ct cts = neToOmega . filterZeros . sumSimilarTerms . NE.sort $ ct :| cts where
  -- [2xy^2, -5xy^2, 3x] -> [-3xy^2, 3x]
  sumSimilarTerms :: NonEmpty (Coterm n) -> NonEmpty (Coterm n)
  sumSimilarTerms (ct :| [])       = ct :| []
  sumSimilarTerms (Coterm cvs c :| Coterm cvs' c' : cts) = if cvs == cvs'
    then sumSimilarTerms $ mkCoterm cvs (c <> c') :| cts
    else Coterm cvs c <| sumSimilarTerms (Coterm cvs' c' :| cts)
  -- remove all terms with 0 as coefficient but
  -- if the result is an empty list, keep one
  filterZeros :: NonEmpty (Coterm n) -> NonEmpty (Coterm n)
  filterZeros = fromMaybe (mempty :| []) . NE.nonEmpty . NE.filter (mempty /=)
  neToOmega (ct :| cts) = Coterms ct cts

evalOmega :: Vec n (V n) -> Omega n -> C n
evalOmega vs (Coterms ct cts) =
  foldr (<>) (evalCoterm vs ct) . fmap (evalCoterm vs) $ cts

extProdCoterm :: Coterm n -> Omega n -> Omega n
extProdCoterm ct' (Coterms ct cts) =
  mkOmega (ct' <> ct) $ fmap ((<>) ct') cts

exteriorProduct :: Omega n -> Omega n -> Omega n
exteriorProduct (Coterms ct cts) o =
  foldr (<>) (extProdCoterm ct o) . fmap (\ct -> extProdCoterm ct o) $ cts

dCotermBy :: Coterm n -> Covar n -> Coterm n
dCotermBy (Coterm cvs c) cv =
  let (Coterm cvs' c') = mkCoterm (cv:cvs) c
  in Coterm cvs' . partialD c' . covarDim $ cv

dCoterm :: SNatI n => Coterm n -> Omega n
dCoterm ct = foldr (<>) mempty . fmap (liftToOmega . dCotermBy ct . Covar) $ V.universe

-- exterior derivative
d :: SNatI n => Omega n -> Omega n
d (Coterms ct cts) = foldr (<>) (dCoterm ct) $ fmap dCoterm cts

