module TestR ( mainR ) where

import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Typeclasses
import R

-- Vectors
type OneR n = R n -> Bool
type TwoR n = R n -> OneR n
type ThreeR n = R n -> TwoR n
type FourR n = R n -> ThreeR n

semigroupSymmetric :: TwoR n
semigroupSymmetric r1 r2 = (r1 <> r2) == (r2 <> r1)

semigroupAssociates :: ThreeR n
semigroupAssociates r1 r2 r3 = ((r1 <> r2) <> r3) == (r1 <> (r2 <> r3))

monoidLeftId :: N.SNatI n => OneR n
monoidLeftId r = (mempty <> r) == r

groupInv :: N.SNatI n => OneR n
groupInv r = r <> ginv r == mempty && ginv r <> r == mempty

moduleAddDistributes1 :: N.SNatI n => Rational -> Rational -> OneR n
moduleAddDistributes1 d1 d2 r =
  mmult d1 r <> mmult d2 r == mmult (d1+d2) r

moduleAddDistributes2 :: N.SNatI n => Rational -> TwoR n
moduleAddDistributes2 d r1 r2 =
  mmult d r1 <> mmult d r2 == mmult d (r1 <> r2)

moduleMultAssociates :: N.SNatI n => Rational -> Rational -> OneR n
moduleMultAssociates d1 d2 r =
  mmult d1 (mmult d2 r) == mmult (d1*d2) r

module1Id :: N.SNatI n => OneR n
module1Id r = mmult (1 :: Rational) r == r

-- Matrices

type OneMat n m = Mat n m -> Bool
type RMat n m = R m -> Mat n m -> Bool
type MatR n m = R n -> Mat n m -> Bool

transpIdenpotent :: (N.SNatI n, N.SNatI m) => OneMat n m
transpIdenpotent m = (transpose . transpose $ m) == m

-- appending a row and multyplying the resulting matrix
-- with a corresponding coordinate vector is identity
rowAppendProdWithCoordVec :: (N.SNatI n, N.SNatI m) => RMat n m
rowAppendProdWithCoordVec r m = vecMatProduct (coordVec F.fin0) (appendRow r m) == r

colAppendProdWithCoordVec :: (N.SNatI n, N.SNatI m) => MatR n m
colAppendProdWithCoordVec r m = matVecProduct (appendCol r m) (coordVec F.fin0) == r

main :: IO ()
main = hspec $ do
  describe "Tests for R, R:" $ do
    prop "semigroup is symmetric"
      (semigroupSymmetric :: TwoR N.Nat3)
    prop "semigroup associative"
      (semigroupAssociates :: ThreeR N.Nat3)
    -- no need to test for right identity because the monoid is symmetric
    prop "monoid left identity"
      (monoidLeftId :: OneR N.Nat3)
    prop "group has inverses"
      (groupInv :: OneR N.Nat3)
    prop "module ring addition distributive"
      (moduleAddDistributes1 :: Rational -> Rational -> OneR N.Nat3)
    prop "module group addition distributive"
      (moduleAddDistributes2 :: Rational -> TwoR N.Nat3)
    prop "module multiplication associative"
      (moduleAddDistributes2 :: Rational -> TwoR N.Nat3)
    prop "module multiplication by 1 is identity"
      (module1Id :: OneR N.Nat3)

  describe "Tests for R, Mat:" $ do
    prop "transpose is idenpotent"
      (transpIdenpotent :: OneMat N.Nat5 N.Nat3)
    prop "appending a row and extracting it is identity"
      (rowAppendProdWithCoordVec :: RMat N.Nat5 N.Nat3)
    prop "appending a col and extracting it is identity"
      (colAppendProdWithCoordVec :: MatR N.Nat5 N.Nat3)


-- rename for exporting
mainR = main

