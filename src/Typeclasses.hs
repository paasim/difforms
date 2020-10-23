{-# LANGUAGE MultiParamTypeClasses #-}
module Typeclasses where

-- Definitions of Semirng, Semiring and Algebra

-- A structure that is linear in the sense that elements
-- can be added and multiplied by rationals
class Monoid g => Group g where
  ginv :: g -> g

-- Assumes that the group is abelian,
-- sums distribute in Rational and g
-- and 1 is multiplicative identity
class Group g => ModuleQ g where
  mqmult :: Rational -> g -> g

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
-- multiplication in Rational in the sense that
-- (amult a g) `sappend` (amult a' g') = amult (a*a') (g `sappend` g')
class Semiring g => Algebra g where
  amult :: Rational -> g -> g

