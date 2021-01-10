{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Common where

import Data.Ratio ( (%) )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Test.QuickCheck

-- Definitions of Semirng, Semiring and Algebra

-- A structure that is linear in the sense that elements
-- can be added and multiplied by rationals
class Monoid g => Group g where
  ginv :: g -> g

class Group g => Module g q | g -> q where
  mmult :: q -> g -> g

-- The monoid is assumed to commute,
-- ie. (a <> b) <> c = a <> (b <> c)
-- The multiplication (semirng-action) should distribute over addition,
-- ie (a <> b) `sappend` c = (a `sappend` c) <> (b `sappend` c)
class Monoid g => Semirng g where
  sappend :: g -> g -> g

-- semirng = semiring without multiplicative _i_dentity
class Semirng g => Semiring g where
  sempty :: g

-- Assumes that mutliplication in g is compatible with
-- multiplication in Number in the sense that
-- (amult a g) `sappend` (amult a' g') = amult (a*a') (g `sappend` g')
class Semiring g => Algebra g where
  amult :: Number -> g -> g


newtype Number = Number Rational deriving (Eq, Ord, Num)

instance Show Number where
  show (Number r) = show r

instance Arbitrary Number where
  arbitrary = do
    num <- arbitrary :: Gen Int
    denom <- arbitrary :: Gen Word
    return . Number $ toInteger num % toInteger (denom + 1)

instance Semigroup Number where
  (<>) = (+)

instance Monoid Number where
  mempty = 0

instance Group Number where
  ginv = negate

instance Semirng Number where
  sappend = (*)

instance Semiring Number where
  sempty = 1

dotProduct :: Vec n Number -> Vec n Number -> Number
dotProduct vn1 vn2 = foldMap id $ V.zipWith sappend vn1 vn2


merge :: Ord a => [a] -> [a] -> [a]
merge []     l     = l
merge l      []    = l
merge (x:xs) (y:ys) = if x < y
  then x : merge xs (y:ys)
  else y : merge (x:xs) ys

combineSimilar :: (a -> a -> Bool) -> (a -> a -> a) -> [a] -> [a]
combineSimilar eq comb [] = []
combineSimilar eq comb (x:[]) = [x]
combineSimilar eq comb (x1:x2:xs) = if eq x1 x2
  then combineSimilar eq comb (comb x1 x2 : xs)
  else x1 : combineSimilar eq comb (x2:xs)

