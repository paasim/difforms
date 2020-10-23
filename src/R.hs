{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module R where

import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Ratio ( (%) )
import Test.QuickCheck
import Typeclasses

-- R n, n-dimensional real numbers
newtype R n = R { x :: Vec n Rational } deriving (Eq, Ord)

instance Show (R n) where
  show (R x) = "(" <> show' x <> ")" where
    show' :: Vec n Rational -> String
    show' VNil         = ""
    show' (xn ::: VNil) = show xn
    show' (xi ::: rest) = show xi <> ", " <> show' rest

-- sum as the monoid
instance Semigroup (R n) where
  r <> r' = R $ V.zipWith (+) (x r) (x r')

instance N.SNatI n => Monoid (R n) where
  mempty = R $ V.repeat 0

instance N.SNatI n => Group (R n) where
  ginv = R . fmap negate . x

instance N.SNatI n => ModuleQ (R n) where
  mqmult d = R . fmap (* d) . x

dotProduct :: N.SNatI n => R n -> R n -> Rational
dotProduct r r' = sum . V.toList $ V.zipWith (*) (x r) (x r')

newtype SimpleRational = SimpleRational (Int, Word)

instance Arbitrary SimpleRational where
  arbitrary = curry SimpleRational <$> arbitrary
                                   <*> arbitrary

simpleRationalToRational :: SimpleRational -> Rational
simpleRationalToRational (SimpleRational (num, denom))
  = toInteger num % toInteger (denom + 1)

genSimpleRational :: Gen Rational
genSimpleRational = simpleRationalToRational <$> arbitrary

genSimpleRationalVec :: N.SNatI n => Gen (Vec n Rational)
genSimpleRationalVec = fmap (fmap simpleRationalToRational) arbitrary

instance N.SNatI n => Arbitrary (R n) where
  arbitrary = R <$> genSimpleRationalVec

coordVec :: N.SNatI n => Fin n -> R n
coordVec n = R . V.imap (\i _ -> if i == n then 1 else 0) $ V.universe

-- Mat n m, Matrices as lists of m-dimensional real numbers
newtype Mat n m = Mat { mat :: Vec n (R m) } deriving (Eq, Ord)

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

matMatProduct :: (N.SNatI n, N.SNatI m, N.SNatI l) => Mat n m -> Mat m l -> Mat n l
matMatProduct m1 m2 =  Mat . fmap (\rm -> vecMatProduct rm m2) . mat $ m1

diagMat :: N.SNatI n => Mat n n
diagMat = Mat . fmap coordVec $ V.universe

