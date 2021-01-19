{-# LANGUAGE DataKinds #-}
module TestI ( testI ) where

import qualified Data.Type.Nat as N
import Data.Vec.Lazy ( Vec(..) )
import Test.Hspec
import Test.Hspec.QuickCheck
import Common
import C
import D
import I


-- I
type OneC n = C n -> Bool
type TwoC n = C n -> OneC n

-- integral linear in Numbers
-- Integral of derivative
-- stokes
type LinearAddI' p n = Vec p (Number, Number) -> D p n -> TwoC n
linearAddI' :: LinearAddI' p n
linearAddI' bs d' c1 c2 =
  (foldMap (evalE bs) . i' c1 $ d') <> (foldMap (evalE bs) . i' c2 $ d')
    == (foldMap (evalE bs) $ i' (c1 <> c2) d')

type LinearMultI' p n = Number -> Vec p (Number, Number) -> D p n -> OneC n
linearMultI' :: LinearMultI' p n
linearMultI' num bs d' c =
  (amult num . foldMap (evalE bs) . i' c $ d')
    == (foldMap (evalE bs) $ i' (amult num c) d')

type LinearAddI p n = Vec n Number -> Vec n Number -> D p n -> TwoC n
linearAddI :: LinearAddI p n
linearAddI from to d' c1 c2 = i from to c1 d' + i from to c2 d'== i from to (c1 <> c2) d'

type LinearMultI p n = Number -> Vec n Number -> Vec n Number -> D p n -> OneC n
linearMultI :: LinearMultI p n
linearMultI num from to d' c = num * (i from to c d') == i from to (amult num c) d'

-- refactor this to use d?
type Stokes1 n = Number -> Number -> Covar n -> OneC n
stokes1 :: Stokes1 n
stokes1 from to cv c =
  let cAtBoundaries = partialEvalC to (covarDim cv) c
        <> ginv (partialEvalC from (covarDim cv) c)
      cSumOfChanges = evalE ((from, to) ::: VNil) $ iE (liftToE $ partialD c (covarDim cv))
                                                       (Coterm (cv ::: VNil) sempty)
  in cAtBoundaries == cSumOfChanges


testI :: IO ()
testI = hspec $ do
  describe "Tests for I, I:" $ do
    prop "addition linear"
      (linearAddI :: LinearAddI N.Nat2 N.Nat3)
    prop "multiplication linear"
      (linearMultI :: LinearMultI N.Nat2 N.Nat3)

  describe "Tests for I, I':" $ do
    prop "addition linear"
      (linearAddI' :: LinearAddI' N.Nat2 N.Nat3)
    prop "multiplication linear"
      (linearMultI' :: LinearMultI' N.Nat2 N.Nat3)

  describe "Tests for I, iE:" $ do
    prop "definition of integral in one dimension"
      (stokes1 :: Stokes1 N.Nat3)

