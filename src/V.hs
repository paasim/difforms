{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module V where

import Data.Type.Nat ( SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Test.QuickCheck
import Common
import R
import C

-- Vector field
newtype V n = V { vComp :: Vec n (C n) }

instance Show (V n) where
  show (V cs) = "V: " <> (L.intercalate "\n   " . V.toList . fmap show $ cs)

instance SNatI n => Arbitrary (V n) where
  arbitrary = V <$> arbitrary

instance Semigroup (V n) where
  v <> v' = V $ V.zipWith (<>) (vComp v) (vComp v')

instance SNatI n => Monoid (V n) where
  mempty = V $ V.repeat mempty

instance SNatI n => Group (V n) where
  ginv = V . fmap ginv . vComp

instance SNatI n => Module (V n) (C n) where
  mmult c = V . fmap (`sappend` c) . vComp

evalV :: SNatI n => C n -> V n -> C n
evalV c v = foldMap id . V.zipWith sappend (vComp v) . fmap (partialD c) $ V.universe

unitV :: SNatI n => V n
unitV = V . V.repeat $ sempty

lieBracket :: SNatI n => V n -> V n -> V n
lieBracket (V v) (V w) = (V . fmap (pdSum v) $ w) <> ginv (V . fmap (pdSum w) $ v) where
  pdSum :: SNatI n => Vec n (C n) -> C n -> C n -- weighted sum of partial derivatives
  pdSum v c = foldMap id . V.zipWith sappend v . fmap (partialD c) $ V.universe


-- Tangent vector at point p
data Vp n = Vp { vpP :: R n, vpV :: Vec n Number }

instance Show (Vp n) where
  show (Vp p v) = "Vp: " <> show (R v) <> "\n at: " <> show p

instance SNatI n => Arbitrary (Vp n) where
  arbitrary = Vp <$> arbitrary <*> arbitrary

evalVp :: SNatI n => C n -> Vp n -> Number
evalVp c (Vp p v) = dotProduct (R v) . R . fmap (evalC p . partialD c) $ V.universe

-- basically a semigroup but this may fail if the base points are not the same...
-- Vp n is a semigroup only when the basepoints are the same
vpappend :: Vp n -> Vp n -> Maybe (Vp n)
vpappend (Vp p1 v1) (Vp p2 v2) = if p1 /= p2 then Nothing else Just . Vp p1 . x $ R v1 <> R v2

-- this is the ModuleQ-multiplication
vpmult :: SNatI n => Number -> Vp n -> Vp n
vpmult d (Vp p v) = Vp p $ fmap (* d) v

vToVp :: V n -> R n -> Vp n
vToVp v r = Vp r . fmap (evalC r) . vComp $ v

unitVp :: SNatI n => Vp n
unitVp = vToVp unitV mempty

