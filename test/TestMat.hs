{-# LANGUAGE DataKinds #-}
module TestMat ( testMat ) where

import Data.Type.Nat ( Nat(..), SNatI )
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Common
import Mat

-- Matrices
type OneMat n m = Mat n m Number -> Bool

type TranspIdenpotent n m = Mat n m Number -> Bool
transpIdenpotent :: (SNatI n, SNatI m) => TranspIdenpotent n m
transpIdenpotent m = (transpose . transpose $ m) == m

type DetOfTransposeEqual n = Mat n n Number -> Bool
detOfTransposeEqual :: (SNatI n) => DetOfTransposeEqual (S n)
detOfTransposeEqual m = (det . transpose) m == det m

testMat :: IO ()
testMat = hspec $ do
    describe "Tests for Mat:" $ do
      prop "transpose is idenpotent"
        (transpIdenpotent :: TranspIdenpotent N.Nat5 N.Nat3)
      prop "determinant of a transpose of a matrix equals it's determinant" $ do
        (detOfTransposeEqual :: DetOfTransposeEqual N.Nat5)
