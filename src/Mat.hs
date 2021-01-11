{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Mat where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Test.QuickCheck
import Common

-- Mat n m, Matrices as lists of m-dimensional real numbers
data Mat n m a = Mat { mat :: Vec n (Vec m a) } deriving (Eq, Ord)

instance Show a => Show (Mat n m a) where
  show (Mat mat) = "Mat:\n[" <> printRows mat <> "]"

instance (Arbitrary a, SNatI n, SNatI m) => Arbitrary (Mat n m a) where
  arbitrary = Mat <$> arbitrary

printRows :: Show a => Vec n (Vec m a) -> String
printRows VNil                 = ""
printRows (r1 ::: VNil)        = show r1
printRows (r1 ::: r2 ::: rest) = show r1 <> ",\n " <> printRows (r2 ::: rest)

appendRow :: Vec m a -> Mat n m a -> Mat (S n) m a
appendRow am (Mat ams) = Mat $ am ::: ams

appendCol :: Vec n a -> Mat n m a -> Mat n (S m) a
appendCol VNil (Mat VNil) = Mat VNil
appendCol (a ::: as) (Mat (row ::: rows)) =
  appendRow (a ::: row) (appendCol as (Mat rows))

matVecProduct :: (Monoid a, Semirng a) => SNatI m => Mat n m a -> Vec m a -> Vec n a
matVecProduct m am = fmap (foldMap id . V.zipWith sappend am) . mat $ m

vecMatProduct :: (Monoid a, Semirng a, SNatI n, SNatI m) => Mat n m a -> Vec n a -> Vec m a
vecMatProduct m = matVecProduct (transpose m)

transpose :: (SNatI m, SNatI m) => Mat n m a -> Mat m n a
transpose (Mat VNil) = Mat . V.repeat $ VNil
transpose (Mat (a ::: as)) = appendCol a . transpose . Mat $ as

matMatProduct :: (Monoid a, Semirng a, SNatI n, SNatI m, SNatI l)
              => Mat n m a -> Mat m l a -> Mat n l a
matMatProduct m1 m2 =  Mat . fmap (vecMatProduct m2) . mat $ m1

sans :: Vec (S n) a -> Vec (S n) (Vec n a)
sans (a ::: VNil) = VNil ::: VNil
sans (a1 ::: a2 ::: as) = let tk = sans (a2 ::: as)
  in (a2 ::: as) ::: fmap (V.cons a1) tk

altSum :: Group a => Bool -> Vec n a -> a
altSum _     VNil       = mempty
altSum True  (a ::: as) = a <> altSum False as
altSum False (a ::: as) = ginv a <> altSum True as

det :: (Semirng a, Group a) => Mat (S n) (S n) a -> a
det (Mat ((a ::: VNil) ::: VNil))               = a
det (Mat ((a ::: as) ::: (a' ::: as') ::: vas)) =
  let heads = a ::: a' ::: fmap V.head vas
      subMats = sans $ as ::: as' ::: fmap V.tail vas
      dets = fmap (det . Mat) subMats
  in altSum True $ V.zipWith sappend heads dets

