module TestPhi ( mainPhi ) where

import qualified Data.Type.Nat as N
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import Phi
import TestHelpers

type PullbackDef n m = Phi n m -> Terms m -> R n -> Bool

pullbackDef :: (N.SNatI n, N.SNatI m) => PullbackDef n m
pullbackDef phi tsm rn = evalTerms (pullback phi tsm) rn ==
                         evalTerms tsm (vecMatProduct rn . phiMat $ phi)


type PushforwardDef n m = Phi n m -> V n -> Terms m -> R n -> Bool

pushforwardDef :: (N.SNatI n, N.SNatI m) => PushforwardDef n m
pushforwardDef phi vn tsm rn =
  evalTerms (evalV (pushforward phi vn) tsm) (vecMatProduct rn . phiMat $ phi) ==
    evalTerms (evalV vn $ pullback phi tsm) rn

-- tests for:
-- pushforward is a functor
type PushforwardId n = V n -> Terms n -> Bool
pushforwardId :: N.SNatI n => PushforwardId n
pushforwardId v ts = evalV (pushforward idPhi v) ts == evalV v ts

type PushforwardComp n m l = Phi n m -> Phi m l -> V n -> Terms l -> Bool
pushforwardComp :: (N.SNatI n, N.SNatI m, N.SNatI l) => PushforwardComp n m l
pushforwardComp phiNM phiML vn tsl =
  evalV (pushforward (compPhi phiNM phiML) vn) tsl ==
    evalV (pushforward phiML . pushforward phiNM $ vn) tsl

-- pushforward is linear
type PushforwardMult n m = Phi n m -> Rational -> V n -> Terms m -> Bool
pushforwardMult :: (N.SNatI n, N.SNatI m) => PushforwardMult n m
pushforwardMult phi r v ts = evalV (vsmult r . pushforward phi $ v) ts
                          == evalV (pushforward phi . vsmult r $ v) ts

type PushforwardAdd n m = Phi n m -> V n -> V n -> Terms m -> Bool
pushforwardAdd :: (N.SNatI n, N.SNatI m) => Phi n m -> V n -> V n -> Terms m -> Bool
pushforwardAdd phi v1 v2 ts =
  evalV (pushforward phi . vsadd v1 $ v2) ts ==
    evalV (vsadd (pushforward phi v1) (pushforward phi v2)) ts

main :: IO ()
main = do
  qc "pullback works as expected"
    (pullbackDef :: PullbackDef N.Nat3 N.Nat2)
  qc "pushforward works as expected"
    (pushforwardDef :: PushforwardDef N.Nat3 N.Nat2)
  qc "pushforward preserves identity"
    (pushforwardId :: PushforwardId N.Nat3)
  qc "pushforward preserves identity"
    (pushforwardComp :: PushforwardComp N.Nat3 N.Nat4 N.Nat2)
  qc "pushforward is preserves multiplication"
    (pushforwardMult :: PushforwardMult N.Nat3 N.Nat2)
  qc "pushforward is preserves addition"
    (pushforwardAdd :: PushforwardAdd N.Nat2 N.Nat3)

-- rename for exporting
mainPhi = main

