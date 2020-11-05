module TestPhi ( mainPhi ) where

import Data.Type.Nat ( SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Type.Nat as N
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import Omega
import Phi
import TestHelpers

type PullbackDefC n m = Phi n m -> C m -> R n -> Bool
pullbackDefC :: (SNatI n, SNatI m) => PullbackDefC n m
pullbackDefC phi cm rn = evalC rn (pullbackC phi cm) ==
                         evalC (evalPhi rn phi) cm

-- pullbackC is a functor
type PullbackCId n = C n -> R n -> Bool
pullbackCId :: SNatI n => PullbackCId n
pullbackCId cn rn = evalC rn (pullbackC idPhi cn) == evalC rn cn

type PullbackCComp n m l = Phi n m -> Phi m l -> C l -> R n -> Bool
pullbackCComp :: (SNatI n, SNatI m, SNatI l) => PullbackCComp n m l
pullbackCComp phiNM phiML cl rn =
  evalC rn (pullbackC (compPhi phiNM phiML) cl) ==
    evalC rn (pullbackC phiNM . pullbackC phiML $ cl)

-- pullback is linear
type PullbackCAdd n m = Phi n m -> R n -> C m -> C m -> Bool
pullbackCAdd :: (SNatI n, SNatI m) => PullbackCAdd n m
pullbackCAdd phi rn cm1 cm2 =
  (evalC rn . pullbackC phi $ cm1 <> cm2)
    == evalC rn (pullbackC phi cm1) + evalC rn (pullbackC phi cm2)

type PullbackCMult n m = Phi n m -> Rational -> R n -> C m -> Bool
pullbackCMult :: (SNatI n, SNatI m) => PullbackCMult n m
pullbackCMult phi r rn cm =
  evalC rn (amult r . pullbackC phi $ cm)
    == evalC rn (pullbackC phi . amult r $ cm)



type PushforwardDef n m = Phi n m -> Vp n -> C m -> Bool
pushforwardDef :: (SNatI n, SNatI m) => PushforwardDef n m
pushforwardDef phi vpn cm =
  evalVp cm (pushforward phi vpn) == evalVp (pullbackC phi cm) vpn

-- tests for:
-- pushforward is a functor
type PushforwardId n = Vp n -> C n -> Bool
pushforwardId :: SNatI n => PushforwardId n
pushforwardId vp c = evalVp c (pushforward idPhi vp) == evalVp c vp

type PushforwardComp n m l = Phi n m -> Phi m l -> Vp n -> C l -> Bool
pushforwardComp :: (SNatI n, SNatI m, SNatI l) => PushforwardComp n m l
pushforwardComp phiNM phiML vpn cl =
  evalVp cl (pushforward (compPhi phiNM phiML) vpn) ==
    evalVp cl (pushforward phiML . pushforward phiNM $ vpn)

-- pushforward is linear
type PushforwardAdd n m = Phi n m -> R n -> Vec n Rational -> Vec n Rational -> C m -> Bool
pushforwardAdd :: (SNatI n, SNatI m) => PushforwardAdd n m
pushforwardAdd phi p v1 v2 c =
  let vp1 = Vp p v1
      vp2 = Vp p v2
 in fmap (evalVp c . pushforward phi) (vpappend vp1 vp2)
      == fmap (evalVp c) (vpappend (pushforward phi vp1) (pushforward phi vp2))

type PushforwardMult n m = Phi n m -> Rational -> Vp n -> C m -> Bool
pushforwardMult :: (SNatI n, SNatI m) => PushforwardMult n m
pushforwardMult phi r vp c = evalVp c (vpmult r . pushforward phi $ vp)
                           == evalVp c (pushforward phi . vpmult r $ vp)

main :: IO ()
main = do
  putStrLn "Tests for Phi:"
  putStrLn "PullbackC:"
  qc "pullbackC works as expected for functions"
    (pullbackDefC :: PullbackDefC N.Nat3 N.Nat2)
  qc "pullback preserves identity"
    (pullbackCId :: PullbackCId N.Nat3)
  qc "pullbackC preserves composition"
    (pullbackCComp :: PullbackCComp N.Nat2 N.Nat3 N.Nat2)
  qc "pullbackC is preserves multiplication"
    (pullbackCMult :: PullbackCMult N.Nat3 N.Nat2)
  qc "pullbackC is preserves addition"
    (pullbackCAdd :: PullbackCAdd N.Nat2 N.Nat3)


  putStrLn "Pushforward:"
  qc "pushforward works as expected"
    (pushforwardDef :: PushforwardDef N.Nat3 N.Nat2)
  qc "pushforward preserves identity"
    (pushforwardId :: PushforwardId N.Nat3)
  qc "pushforward preserves composition"
    (pushforwardComp :: PushforwardComp N.Nat2 N.Nat3 N.Nat2)
  qc "pushforward is preserves multiplication"
    (pushforwardMult :: PushforwardMult N.Nat3 N.Nat2)
  qc "pushforward is preserves addition"
    (pushforwardAdd :: PushforwardAdd N.Nat2 N.Nat3)

-- rename for exporting
mainPhi = main

