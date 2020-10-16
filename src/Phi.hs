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
import Typeclasses
import R
import C
import V

-- Linear maps (instead of any diffeomorphism)
type Phi' n m = Mat n m --Phi' { matPhi :: Vec m (Vec n Rational) }

-- not endomap due to term not containing sums
pullbackTerm :: N.SNatI m => Phi' n m -> Term m -> Terms n
pullbackTerm _   (Term d [])             = liftToTerms . liftToTerm $ d
pullbackTerm phi (Term d (Var ind exp : ts)) =
  -- given coefficient d' and index i, constructs a term
  let termWithCoef i d' = liftToTerms $ Term d' [Var i 0]
  -- construct the sum of terms given a cofficient vector (of type R n)
      sumTerms = V.ifoldr (\i d' -> (<>) (termWithCoef i d')) mempty . x
  -- picks the correct vector from phi and multiplies with the other terms recursively
  in sappend (nthPower (exp+1) . sumTerms $ mat (transpose phi) V.! ind)
             (pullbackTerm phi $ Term d ts)

-- precomposes f with the manifold map
pullback :: N.SNatI m => Phi' n m -> Terms m -> Terms n
pullback phi (Terms (t1 :| []))    = pullbackTerm phi t1
pullback phi (Terms (t1 :| t2:ts)) = pullbackTerm phi t1 <> pullback phi (Terms (t2 :| ts))


pushforward :: (N.SNatI n, N.SNatI m) => Phi' n m -> V n -> V m
pushforward m v = V $ vecMatProduct (vCoeff v) m

