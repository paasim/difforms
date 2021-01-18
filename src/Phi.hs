{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Phi where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Test.QuickCheck
import Common
import Mat
import C
import V
import D

-- Map from R n to R m defined componentwise,
-- phi_i defines how i:th element depends on R n
newtype Phi n m = Phi { phiComp :: Vec m (C n) }

instance (SNatI n, SNatI m) => Show (Phi n m) where
  show = (<>) "Phi:\n " . L.intercalate "\n "
       . V.toList . fmap showStrAsFun
       . V.zipWith (,) V.universe . fmap show . phiComp

showStrAsFun :: (Fin n, String) -> String
showStrAsFun (n, str) = str <> " -> x_" <> show n

genSimpleC :: SNatI n => Gen (C n)
genSimpleC = mkC <$> resize 2 arbitrary

-- this is kind of hacky, but dont know another way
-- of running genSimpleC over a Vec
genSimpleCs :: (SNatI m, SNatI n) => Gen (Vec m (C n))
genSimpleCs = traverse (const genSimpleC) $ V.repeat ()

-- Cs that contain at most two terms because the
-- computations become quite expensive if the sums
-- contain more terms
instance (SNatI n, SNatI m) => Arbitrary (Phi n m) where
  arbitrary = Phi <$> genSimpleCs

evalPhi :: Vec n Number -> Phi n m -> Vec m Number
evalPhi vn = fmap (evalC vn) . phiComp

-- if f = phi x_m, pullback x_m = f^exp
pullbackVar :: Phi n m -> Var m -> C n
pullbackVar phi (Var n e) = nthPower (S e) $ phiComp phi V.! n

-- folds over vars
pullbackTerm :: Phi n m -> Term m -> C n
pullbackTerm _ ZeroTerm      = liftToC ZeroTerm
pullbackTerm phi (Term vs num) =
  foldr sappend (liftToC $ liftToTerm num) $ fmap (pullbackVar phi) vs

-- precomposes f with the manifold map,
-- folds over terms
pullbackC :: Phi n m -> C m -> C n
pullbackC phi = foldMap (pullbackTerm phi) . cTerms

pullbackCovar :: SNatI n => Phi n m -> Covar m -> D (S Z) n
pullbackCovar phi cv = d0 $ phiComp phi V.! covarDim cv

pullbackCoterm :: SNatI n => Phi n m -> Coterm p m -> D p n
pullbackCoterm phi (Coterm VNil c) = liftToD . liftToCoterm . pullbackC phi $ c
pullbackCoterm phi (Coterm (cv:::cvs) c) =
  exteriorProduct (pullbackCovar phi cv) . pullbackCoterm phi $ Coterm cvs c

pullbackD :: SNatI n => Phi n m -> D p m -> D p n
pullbackD phi = foldMap (pullbackCoterm phi) . dCoterms

-- evaluates phi (p ,v) componentwise
pushforward :: (SNatI n, SNatI m) => Phi n m -> Vp n -> Vp m
pushforward phi (Vp p v) =
  Vp (evalPhi p phi) $ vecMatProduct (jacobianAt phi p) v

-- identity map
idPhi :: SNatI n => Phi n n
idPhi = Phi . fmap (\n -> liftToC . Term [Var n 0] $ 1) $ V.universe

-- composition is the same as pullback over the columns
-- eg compose 2x^2->y 3y^3->_ = 3*(2x^2)^3 = 3*(24x^6) = 72x^6
compPhi :: (SNatI n, SNatI m, SNatI l) => Phi n m -> Phi m l -> Phi n l
compPhi phiNM = Phi . fmap (pullbackC phiNM) . phiComp

jacobianAt :: SNatI n => Phi n m -> Vec n Number -> Mat n m Number
jacobianAt phi rn = transpose . Mat . fmap (gradientAt rn) . phiComp $ phi

jacobian :: SNatI n => Phi n m -> Vec m (Vec n (C n))
jacobian = fmap gradient . phiComp

jacobianToAt :: SNatI n => Vec m (Vec n (C n)) -> Vec n Number -> Mat n m Number
jacobianToAt j r = transpose . Mat . fmap (fmap (evalC r)) $ j

