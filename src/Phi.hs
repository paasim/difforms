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
pullbackTerm phi (Term d []) = liftToC . liftToTerm $ d
pullbackTerm phi (Term d (Var n exp : ts)) =
  sappend (nthPower (exp+1) $ phiComp phi V.! n) (pullbackTerm phi $ Term d ts)

-- precomposes f with the manifold map
pullback :: Phi n m -> C m -> C n
pullback phi (Terms (t1 :| []))    = pullbackTerm phi t1
pullback phi (Terms (t1 :| t2:ts)) = pullbackTerm phi t1 <> pullback phi (Terms $ t2 :| ts)

pushforward :: (SNatI n, SNatI m) => Phi n m -> Vp n -> Vp m
pushforward phi (Vp p v) = Vp (evalPhi p phi)
                              (x $ vecMatProduct (R v) (jacobianAt phi p))

idPhi :: SNatI n => Phi n n
idPhi = Phi . fmap (\n -> liftToC . mkTerm 1 $ [Var n 0]) $ V.universe

compPhi :: (SNatI n, SNatI m, SNatI l) => Phi n m -> Phi m l -> Phi n l
compPhi phiNM = Phi . fmap (pullback phiNM) . phiComp

showStrAsFun :: Fin n -> String -> String
showStrAsFun n str = str <> " -> x_" <> show n

jacobianAt :: SNatI n => Phi n m -> R n -> Mat n m
jacobianAt phi rn = transpose . Mat . fmap (gradientAt rn) . phiComp $ phi

-- pullbacks and pushforwards for Omega/OmegaP missing

