{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module V where

import qualified Data.Map.Strict as M
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Test.QuickCheck
import Algebra
import R
import Phi
import C

newtype V n = V { vCoeff :: R n }

instance N.SNatI n => Arbitrary (V n) where
  arbitrary = V <$> arbitrary

-- this is just a different representation for C.tangent
evalV :: N.SNatI n => V n -> C' n -> C' n
evalV (V v) c = foldr (<>) mempty . V.zipWith amult (x v) . fmap (\n -> partialD n c) $ V.universe

pushforward :: (N.SNatI n, N.SNatI m) => Phi' n m -> V n -> V m
pushforward m v = V $ vecMatProduct (vCoeff v) m

