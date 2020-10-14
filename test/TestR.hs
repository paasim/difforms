module TestR ( mainR ) where

import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Test.QuickCheck
import Typeclasses
import R

-- Vectors
type OneR n = R n -> Bool
type TwoR n = R n -> OneR n
type ThreeR n = R n -> TwoR n
type FourR n = R n -> ThreeR n

semigroupSymmetric :: TwoR n
semigroupSymmetric r1 r2 = (r1 <> r2) == (r2 <> r1)

semigroupCommutes :: ThreeR n
semigroupCommutes r1 r2 r3 = ((r1 <> r2) <> r3) == (r1 <> (r2 <> r3))

monoidLeftId :: N.SNatI n => OneR n
monoidLeftId r = (mempty <> r) == r

semirngCommutes :: N.SNatI n => ThreeR n
semirngCommutes r1 r2 r3 = ((r1 `sappend` r2) `sappend` r3)
  == (r1 `sappend` (r2 `sappend` r3))

semirngLeftId :: N.SNatI n => OneR n
semirngLeftId r = (sempty `sappend` r) == r

semirngRightId :: N.SNatI n => OneR n
semirngRightId r = (r `sappend` sempty) == r

semiringDistributes :: N.SNatI n => FourR n
semiringDistributes r1 r2 r3 r4 = ((r1 <> r2) `sappend` (r3 <> r4))
  == ((r1 `sappend` r3) <> (r1 `sappend` r4) <> (r2 `sappend` r3) <> (r2 `sappend` r4))

semiringLeftAnnih :: N.SNatI n => OneR n
semiringLeftAnnih r = mempty `sappend` r == mempty

semiringRightAnnih :: N.SNatI n => OneR n
semiringRightAnnih r = r `sappend` mempty == mempty

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
main = do
  quickCheck (semigroupSymmetric  :: TwoR N.Nat3)
  quickCheck (semigroupCommutes   :: ThreeR N.Nat3)
  -- no need to test for right identity because the monoid is symmetric
  quickCheck (monoidLeftId        :: OneR N.Nat3)
  quickCheck (semirngCommutes     :: ThreeR N.Nat3)
  quickCheck (semirngLeftId       :: OneR N.Nat3)
  quickCheck (semirngRightId      :: OneR N.Nat3)
  quickCheck (semiringDistributes :: FourR N.Nat3)
  quickCheck (semiringLeftAnnih   :: OneR N.Nat3)
  quickCheck (semiringRightAnnih  :: OneR N.Nat3)

  quickCheck (transpIdenpotent :: OneMat N.Nat5 N.Nat3)
  quickCheck (rowAppendProdWithCoordVec :: RMat N.Nat5 N.Nat3)
  quickCheck (colAppendProdWithCoordVec :: MatR N.Nat5 N.Nat3)


-- rename for exporting
mainR = main

