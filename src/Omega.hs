{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Omega where

import qualified Data.Map.Strict as M
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import Data.Fin ( Fin(..) )
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


-- dx, dy etc
newtype Covar n = Covar { covarDim :: Fin n } deriving (Eq, Ord)

instance Show (Covar n) where
  show (Covar n)    = "d_" <> show n

evalCovar :: V n -> Covar n -> C n
evalCovar v (Covar n) = vComp v V.! n

instance N.SNatI n => Arbitrary (Covar n) where
  arbitrary = Covar <$> (elements . V.toList $ V.universe)


-- (Exterior) products of covars with a C n coefficient
data Coterm n = Coterm { cotermVars :: Set (Covar n), cotermCoeff :: C n } deriving (Eq, Ord)

evalCoterm :: Vec n (V n) -> Coterm n -> C n
evalCoterm vs (Coterm cvs c') = sappend c' . foldr sappend sempty
  $ zipWith evalCovar (V.toList vs) (S.toList cvs)

instance Show (Coterm n) where
  show (Coterm cvs c) = if S.null cvs
    then show c
    else "(" <> show c <> ")*" <> (L.intercalate "*" . fmap show  . S.toList $ cvs)

appendCovar :: Covar n -> Coterm n -> Coterm n
appendCovar cv (Coterm cvs c) = if S.member cv cvs
  then Coterm S.empty mempty
  else let cvs' = S.insert cv cvs
           ind = S.findIndex cv cvs'
           len = S.size cvs'
           -- determine whether adding cv corresponds to odd or even # of swaps
           c' = if mod (len - 1 - ind) 2 == 0 then c else ginv c
       in Coterm cvs' c'

prependCovar :: Covar n -> Coterm n -> Coterm n
prependCovar cv (Coterm cvs c) = if S.member cv cvs
  then Coterm S.empty mempty
  else let cvs' = S.insert cv cvs
           ind = S.findIndex cv cvs'
           c' = if mod ind 2 == 0 then c else ginv c
       in Coterm cvs' c'


mkCoterm :: C n -> [Covar n] -> Coterm n
mkCoterm c = foldr appendCovar (liftToCoterm c) . reverse

liftToCoterm :: C n -> Coterm n
liftToCoterm c = Coterm S.empty c

instance Semigroup (Coterm n) where
  (Coterm cvs c) <> (Coterm cvs' c') = mkCoterm (c `sappend` c') (S.toList cvs <> S.toList cvs')

instance Monoid (Coterm n) where
  mempty = liftToCoterm mempty

negateCoterm :: Coterm n -> Coterm n
negateCoterm (Coterm cvs c) = Coterm cvs $ ginv c

instance N.SNatI n => Arbitrary (Coterm n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkCoterm <$> arbitrary
                       <*> resize 2 (listOf arbitrary)


-- n-forms from n-manifold, hopefully these could be refactored
-- into p-forms (where p<=n)
data Omega n = Coterms (Coterm n) [Coterm n] deriving Show

mkOmega :: Coterm n -> [Coterm n] -> Omega n
mkOmega ct cts = neToOmega . filterZeros . sumSimilarTerms . NE.sort $ ct :| cts where
  -- [2xy^2, -5xy^2, 3x] -> [-3xy^2, 3x]
  sumSimilarTerms :: NonEmpty (Coterm n) -> NonEmpty (Coterm n)
  sumSimilarTerms (ct :| [])       = ct :| []
  sumSimilarTerms (Coterm cvs c :| Coterm cvs' c' : cts) = if cvs == cvs'
    then sumSimilarTerms $ mkCoterm (c <> c') (S.toList cvs) :| cts
    else Coterm cvs c <| sumSimilarTerms (Coterm cvs' c' :| cts)
  -- remove all terms with 0 as coefficient but
  -- if the result is an empty list, keep one
  filterZeros :: NonEmpty (Coterm n) -> NonEmpty (Coterm n)
  filterZeros = fromMaybe (mempty :| []) . NE.nonEmpty . NE.filter (mempty /=)
  neToOmega (ct :| cts) = Coterms ct cts


ctMultByC :: C n -> Coterm n -> Coterm n
ctMultByC c' (Coterm cvs c) = Coterm cvs (sappend c c')


liftToOmega :: Coterm n -> Omega n
liftToOmega ct = mkOmega ct []

instance Semigroup (Omega n) where
  (Coterms c1 c1s) <> (Coterms c2 c2s) = mkOmega c1 (c1s <> (c2 : c2s))

instance Monoid (Omega n) where
  mempty = liftToOmega . liftToCoterm $ mempty

-- Being (Abelian) Group and Semiring makes it a Ring
instance Group (Omega n) where
  ginv (Coterms t ts) = mkOmega (negateCoterm t) $ fmap negateCoterm ts

instance Module (Omega n) (C n) where
  mmult c (Coterms ct cts) = mkOmega (ctMultByC c ct) $ fmap (ctMultByC c) cts

extProdCovar :: Omega n -> Covar n -> Omega n
extProdCovar (Coterms ct cts) cv =
  mkOmega (appendCovar cv ct) $ fmap (appendCovar cv) cts where

extProdCoterm :: Coterm n -> Omega n -> Omega n
extProdCoterm (Coterm cvs c) v = mmult c $ foldl extProdCovar v cvs

exteriorProduct :: Omega n -> Omega n -> Omega n
exteriorProduct (Coterms ct cts) v =
  foldr extProdCoterm (extProdCoterm ct v) cts

evalOmega :: Vec n (V n) -> Omega n -> C n
evalOmega vs (Coterms ct cts) = foldr (<>) mempty . fmap (evalCoterm vs) $ ct:cts

instance N.SNatI n => Arbitrary (Omega n) where
  arbitrary = mkOmega <$> arbitrary <*> resize 4 (listOf arbitrary)

dCotermBy :: Coterm n -> Fin n -> Coterm n
dCotermBy ct n =
  let (Coterm cvs' c') = prependCovar (Covar n) ct
  in Coterm cvs' $ partialD c' n

dCoterm :: N.SNatI n => Coterm n -> Omega n
dCoterm ct = foldr (<>) mempty . fmap (liftToOmega . dCotermBy ct) $ V.universe

-- exterior derivative
d :: N.SNatI n => Omega n -> Omega n
d (Coterms ct cts) = foldr (<>) (dCoterm ct) $ fmap dCoterm cts

d' :: N.SNatI n => C n -> Omega n
d' = d . liftToOmega . liftToCoterm

