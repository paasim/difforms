module TestPhi ( mainPhi ) where

import qualified Data.Type.Nat as N
import Data.Vec.Lazy ( Vec(..) )
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import Phi
import TestHelpers

type PullbackDef n m = Phi n m -> C m -> R n -> Bool
pullbackDef :: (N.SNatI n, N.SNatI m) => PullbackDef n m
pullbackDef phi cm rn = evalC rn (pullback phi cm) ==
                         evalC (evalPhi rn phi) cm


type PushforwardDef n m = Phi n m -> Vp n -> C m -> Bool
pushforwardDef :: (N.SNatI n, N.SNatI m) => PushforwardDef n m
pushforwardDef phi vpn cm =
  evalVp cm (pushforward phi vpn) == evalVp (pullback phi cm) vpn

-- tests for:
-- pushforward is a functor
type PushforwardId n = Vp n -> C n -> Bool
pushforwardId :: N.SNatI n => PushforwardId n
pushforwardId vp c = evalVp c (pushforward idPhi vp) == evalVp c vp

type PushforwardComp n m l = Phi n m -> Phi m l -> Vp n -> C l -> Bool
pushforwardComp :: (N.SNatI n, N.SNatI m, N.SNatI l) => PushforwardComp n m l
pushforwardComp phiNM phiML vpn cl =
  evalVp cl (pushforward (compPhi phiNM phiML) vpn) ==
    evalVp cl (pushforward phiML . pushforward phiNM $ vpn)

-- pushforward is linear
type PushforwardAdd n m = Phi n m -> R n -> Vec n Rational -> Vec n Rational -> C m -> Bool
pushforwardAdd :: (N.SNatI n, N.SNatI m) => PushforwardAdd n m
pushforwardAdd phi p v1 v2 c =
  let vp1 = Vp p v1
      vp2 = Vp p v2
 in fmap (evalVp c . pushforward phi) (vpappend vp1 vp2)
      == fmap (evalVp c) (vpappend (pushforward phi vp1) (pushforward phi vp2))

type PushforwardMult n m = Phi n m -> Rational -> Vp n -> C m -> Bool
pushforwardMult :: (N.SNatI n, N.SNatI m) => PushforwardMult n m
pushforwardMult phi r vp c = evalVp c (vpmult r . pushforward phi $ vp)
                           == evalVp c (pushforward phi . vpmult r $ vp)

main :: IO ()
main = do
  putStrLn "tests for Phi:"
  qc "pullback works as expected"
    (pullbackDef :: PullbackDef N.Nat3 N.Nat2)
  qc "pushforward works as expected"
    (pushforwardDef :: PushforwardDef N.Nat3 N.Nat2)
  qc "pushforward preserves identity"
    (pushforwardId :: PushforwardId N.Nat3)
  qc "pushforward preserves composition"
    (pushforwardComp :: PushforwardComp N.Nat3 N.Nat4 N.Nat2)
  qc "pushforward is preserves multiplication"
    (pushforwardMult :: PushforwardMult N.Nat3 N.Nat2)
  qc "pushforward is preserves addition"
    (pushforwardAdd :: PushforwardAdd N.Nat2 N.Nat3)

-- rename for exporting
mainPhi = main

