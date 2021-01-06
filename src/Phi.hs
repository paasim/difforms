{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Phi where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List as L
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import D

-- Map from R n to R m defined componentwise,
-- phi_i defines how i:th element depends on R n
newtype Phi n m = Phi { phiComp :: Vec m (C n) } deriving (Eq, Ord)

instance (SNatI n, SNatI m) => Show (Phi n m) where
  show = (<>) "Phi:\n " . L.intercalate "\n "
       . V.toList . fmap (uncurry showStrAsFun)
       . V.zipWith (,) V.universe . fmap show . phiComp

instance (SNatI n, SNatI m) => Arbitrary (Phi n m) where
  arbitrary = Phi <$> arbitrary

evalPhi :: R n -> Phi n m -> R m
evalPhi rn = R . fmap (evalC rn) . phiComp


pullbackTerm :: Phi n m -> Term m -> C n
pullbackTerm phi (Term [] d) = liftToC . liftToTerm $ d
pullbackTerm phi (Term (Var n exp : vs) d) =
  sappend (nthPower (S exp) $ phiComp phi V.! n) (pullbackTerm phi $ Term vs d)

-- precomposes f with the manifold map
pullbackC :: Phi n m -> C m -> C n
pullbackC phi (Terms t1 [])      = pullbackTerm phi t1
pullbackC phi (Terms t1 (t2:ts)) = pullbackTerm phi t1 <> pullbackC phi (Terms t2 ts)

pushforward :: (SNatI n, SNatI m) => Phi n m -> Vp n -> Vp m
pushforward phi (Vp p v) = Vp (evalPhi p phi)
                              (x $ vecMatProduct (R v) (jacobianAt phi p))

idPhi :: SNatI n => Phi n n
idPhi = Phi . fmap (\n -> liftToC . mkTerm [Var n Z] $ 1) $ V.universe

compPhi :: (SNatI n, SNatI m, SNatI l) => Phi n m -> Phi m l -> Phi n l
compPhi phiNM = Phi . fmap (pullbackC phiNM) . phiComp

showStrAsFun :: Fin n -> String -> String
showStrAsFun n str = str <> " -> x_" <> show n

jacobianAt :: SNatI n => Phi n m -> R n -> Mat n m
jacobianAt phi rn = transpose . Mat . fmap (gradientAt rn) . phiComp $ phi

jacobian :: SNatI n => Phi n m -> Vec m (Vec n (C n))
jacobian = fmap gradient . phiComp

jacobianToAt :: SNatI n => Vec m (Vec n (C n)) -> R n -> Mat n m
jacobianToAt j r = transpose . Mat . fmap (R . fmap (evalC r)) $ j

pullbackCovar :: SNatI n => Phi n m -> Covar m -> D (S Z) n
pullbackCovar phi cv = d0 $ phiComp phi V.! covarDim cv

pullbackCoterm :: SNatI n => Phi n m -> Coterm p m -> D p n
pullbackCoterm _ ZeroCoterm = liftToD ZeroCoterm
pullbackCoterm phi (Coterm VNil c) = liftToD . liftToCoterm . pullbackC phi $ c
pullbackCoterm phi (Coterm (cv:::cvs) c) =
  exteriorProduct (pullbackCovar phi cv) . pullbackCoterm phi $ Coterm cvs c

pullbackD :: SNatI n => Phi n m -> D p m -> D p n
pullbackD phi (Coterms ctp ctps) =
  foldr (<>) (pullbackCoterm phi ctp) $ fmap (pullbackCoterm phi) ctps

