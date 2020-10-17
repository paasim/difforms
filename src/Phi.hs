{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Phi where

import qualified Data.Map.Strict as M
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List as L ( intercalate )
import Test.QuickCheck
import Typeclasses
import R
import C
import V

-- Linear maps (instead of any diffeomorphism)
newtype Phi n m = Phi { phiMat :: Mat n m } deriving (Eq, Ord)

showElemAsFun :: Fin n -> Rational -> String
showElemAsFun n r = show r <> "*x_" <> show n

showVecAsFun :: N.SNatI n => R n -> String
showVecAsFun = L.intercalate " + " . V.toList . fmap (uncurry showElemAsFun) . V.zipWith (,) V.universe . x

showStrAsFun :: Fin n -> String -> String
showStrAsFun n str = str <> " -> x_" <> show n

showMatAsFun :: (N.SNatI n, N.SNatI m) => Mat n m -> String
showMatAsFun = L.intercalate "\n" . V.toList . fmap (uncurry showStrAsFun)
             . V.zipWith (,) V.universe . fmap showVecAsFun . mat . transpose

instance (N.SNatI n, N.SNatI m) => Show (Phi n m) where
  show = showMatAsFun . phiMat

idPhi :: N.SNatI n => Phi n n
idPhi = Phi diagMat

compPhi :: (N.SNatI n, N.SNatI m, N.SNatI l) => Phi n m -> Phi m l -> Phi n l
compPhi (Phi matNM) (Phi matML) = Phi $ matMatProduct matNM matML

-- not endomap due to term not containing sums
pullbackTerm :: N.SNatI m => Phi n m -> Term m -> Terms n
pullbackTerm _   (Term d [])             = liftToTerms . liftToTerm $ d
pullbackTerm phi (Term d (Var ind exp : ts)) =
  -- given coefficient d' and index i, constructs a term
  let termWithCoef i d' = liftToTerms $ Term d' [Var i 0]
  -- construct the sum of terms given a cofficient vector (of type R n)
      sumTerms = V.ifoldr (\i d' -> (<>) (termWithCoef i d')) mempty . x
  -- picks the correct vector from phi and multiplies with the other terms recursively
  in sappend (nthPower (exp+1) . sumTerms $ mat (transpose . phiMat $ phi) V.! ind)
             (pullbackTerm phi $ Term d ts)

instance (N.SNatI n, N.SNatI m) => Arbitrary (Phi n m) where
  arbitrary = Phi <$> arbitrary
-- precomposes f with the manifold map
pullback :: N.SNatI m => Phi n m -> Terms m -> Terms n
pullback phi (Terms (t1 :| []))    = pullbackTerm phi t1
pullback phi (Terms (t1 :| t2:ts)) = pullbackTerm phi t1 <> pullback phi (Terms (t2 :| ts))


pushforward :: (N.SNatI n, N.SNatI m) => Phi n m -> V n -> V m
pushforward phi v = V $ vecMatProduct (vCoeff v) (phiMat phi)

