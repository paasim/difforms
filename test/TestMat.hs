{-# LANGUAGE DataKinds #-}
module TestMat ( testMat ) where

import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.Type.Nat ( Nat(..), SNatI )
import qualified Data.Type.Nat as N
import Data.Vec.Lazy ( Vec(..) )
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Common
import Mat

-- Matrices
type OneMat n m = Mat n m Number -> Bool

type MatVecIdentical n m = Vec m Number -> OneMat n m
matVecIdentical :: (SNatI n, SNatI m) => MatVecIdentical n m
matVecIdentical v m =
  transpose (Mat (matVecProduct m v ::: VNil)) == matMatProduct m (transpose $ Mat (v ::: VNil))

type VecMatIdentical n m = Vec n Number -> OneMat n m
vecMatIdentical :: (SNatI n, SNatI m) => VecMatIdentical n m
vecMatIdentical v m =
  Mat (vecMatProduct m v ::: VNil) == matMatProduct (Mat $ v ::: VNil) m

type TranspIdenpotent n m = OneMat n m
transpIdenpotent :: (SNatI n, SNatI m) => TranspIdenpotent n m
transpIdenpotent m = (transpose . transpose $ m) == m

type DetOfTransposeEqual n = OneMat n n
detOfTransposeEqual :: SNatI n => DetOfTransposeEqual (S n)
detOfTransposeEqual m = (det . transpose) m == det m

type DetProdIdentical n = Mat n n Number -> OneMat n n
detProdIdentical :: SNatI n => DetProdIdentical (S n)
detProdIdentical m1 m2 = sappend (det m1) (det m2) == det (matMatProduct m1 m2)

testMat :: IO ()
testMat = hspec $ do
    describe "Tests for Mat:" $ do
      prop "matMatProduct works identically with matVecProduct"
        (matVecIdentical :: MatVecIdentical N.Nat4 N.Nat3)
      prop "vecMatProduct works identically with matMatProduct"
        (vecMatIdentical :: VecMatIdentical N.Nat4 N.Nat3)
      prop "transpose is idenpotent"
        (transpIdenpotent :: TranspIdenpotent N.Nat5 N.Nat3)
      prop "determinant of a transpose of a matrix equals it's determinant"
        (detOfTransposeEqual :: DetOfTransposeEqual N.Nat5)
      prop "determinant of a product is product of the determinants"
        (detProdIdentical :: DetProdIdentical N.Nat3)

