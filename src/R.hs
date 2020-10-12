{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module R where

import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Test.QuickCheck
import Algebra

-- R n, n-dimensional real numbers
newtype R n = R { x :: Vec n Double } deriving (Eq, Ord)

instance Show (R n) where
  show (R x) = "(" <> show' x <> ")" where
    show' :: Vec n Double -> String
    show' VNil         = ""
    show' (xn ::: VNil) = show xn
    show' (xi ::: rest) = show xi <> ", " <> show' rest

-- sum as the monoid
instance Semigroup (R n) where
  (R x) <> (R x') = R $ V.zipWith (+) x x'

instance N.SNatI n => Monoid (R n) where
  mempty = R $ V.repeat 0

-- multiplication as the semiring
instance N.SNatI n => Semirng (R n) where
  sappend (R x) (R x') = R $ V.zipWith (*) x x'

instance N.SNatI n => Semiring (R n) where
  sempty = R $ V.repeat 1

dotProduct :: N.SNatI n => R n -> R n -> Double
dotProduct pt = sum . x . sappend pt

-- sample just integers for simplicity
instance N.SNatI n => Arbitrary (R n) where
  arbitrary = R . fmap fromInteger <$> arbitrary

coordVec :: N.SNatI n => Fin n -> R n
coordVec n = R . V.imap (\i _ -> if i == n then 1 else 0) $ V.universe

-- Mat n m, Matrices as lists of m-dimensional real numbers
newtype Mat n m = Mat { mat :: Vec n (R m) }

printRows :: Vec m (R n) -> String
printRows VNil                 = ""
printRows (r1 ::: VNil)        = show r1
printRows (r1 ::: r2 ::: rest) = show r1 <> ",\n " <> printRows (r2 ::: rest)

instance Show (Mat n m) where
  show (Mat mat) = "[" <> printRows mat <> "]"

instance (N.SNatI n, N.SNatI m) => Arbitrary (Mat n m) where
  arbitrary = Mat <$> arbitrary

appendRow :: R m -> Mat n m -> Mat (S n) m
appendRow rm (Mat m) = Mat $ rm ::: m

appendCol :: R n -> Mat n m -> Mat n (S m)
appendCol (R VNil) (Mat VNil) = Mat VNil
appendCol (R (d ::: ds)) (Mat ((R row) ::: rows)) = 
  appendRow (R (d ::: row)) (appendCol (R ds) (Mat rows))

matVecProduct :: N.SNatI m => Mat n m -> R m -> R n
matVecProduct (Mat m) r = R . fmap (dotProduct r) $ m

vecMatProduct :: (N.SNatI n, N.SNatI m) => R n -> Mat n m -> R m
vecMatProduct r m = matVecProduct (transpose m) r

transpose :: (N.SNatI m, N.SNatI m) => Mat n m -> Mat m n
transpose (Mat VNil) = Mat . V.repeat . R $ VNil
transpose (Mat (r1 ::: rest)) = appendCol r1 . transpose . Mat $ rest

diagMat :: N.SNatI n => Mat n n
diagMat = Mat . fmap coordVec $ V.universe

