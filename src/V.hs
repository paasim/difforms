{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module V where

import qualified Data.Map.Strict as M
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import qualified Data.List as L ( intercalate )
import Test.QuickCheck
import Typeclasses
import R
import C

-- Vector field
newtype V n = V { vComp :: Vec n (Terms n) }

instance Show (V n) where
  show (V v) = "V: (" <> (L.intercalate ", " . V.toList . fmap show $ v) <> ")"

instance N.SNatI n => Arbitrary (V n) where
  arbitrary = V <$> arbitrary

instance Semigroup (V n) where
  v <> v' = V $ V.zipWith (<>) (vComp v) (vComp v')

instance N.SNatI n => Monoid (V n) where
  mempty = V $ V.repeat mempty

instance N.SNatI n => Group (V n) where
  ginv = V . fmap ginv . vComp

-- V n is a module over C n
-- Assumes that the group is abelian,
-- sums distribute in C n and g
-- and there is multiplicative identity in Cn
vmult :: C n -> V n -> V n
vmult c = V . fmap (`sappend` c) . vComp

evalV :: N.SNatI n => V n -> C n -> C n
evalV (V v) c = foldr (<>) mempty . V.zipWith sappend v . fmap (\n -> partialD n c) $ V.universe

unitV :: N.SNatI n => V n
unitV = V . V.repeat $ sempty


-- Tangent vector at point p
data Vp n = Vp { vpP :: R n, vpV :: Vec n Rational }

instance Show (Vp n) where
  show (Vp p v) = "Vp: " <> show (R v) <> "\n at: " <> show p

instance N.SNatI n => Arbitrary (Vp n) where
  arbitrary = Vp <$> arbitrary <*> genSimpleRationalVec

-- basically a semigroup but this may fail if the base points are not the same...
-- Vp n is a semigroup only when the basepoints are the same
vpappend :: Vp n -> Vp n -> Maybe (Vp n)
vpappend (Vp p1 v1) (Vp p2 v2) = if p1 /= p2 then Nothing else Just . Vp p1 . x $ R v1 <> R v2

-- this is the ModuleQ-multiplication
vpmult :: N.SNatI n => Rational -> Vp n -> Vp n
vpmult d (Vp p v) = Vp p $ fmap (* d) v

vToVp :: V n -> R n -> Vp n
vToVp v r = Vp r . fmap (\ts -> evalTerms ts r) . vComp $ v

evalVp :: N.SNatI n => Vp n -> C n -> Rational
evalVp (Vp p v) c = dotProduct (R v) . R . fmap (\n -> evalTerms (partialD n c) p) $ V.universe

unitVp :: N.SNatI n => Vp n
unitVp = vToVp unitV mempty

