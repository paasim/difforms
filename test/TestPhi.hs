module TestPhi ( mainPhi ) where

import Data.Type.Nat ( SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Type.Nat as N
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Typeclasses
import R
import C
import V
import D
import Phi

-- pullbackC
type PullbackDefC n m = Phi n m -> C m -> R n -> Bool
pullbackDefC :: (SNatI n, SNatI m) => PullbackDefC n m
pullbackDefC phi cm rn = evalC rn (pullbackC phi cm) ==
                         evalC (evalPhi rn phi) cm
-- pullbackC is a functor
type PullbackCId n = C n -> Bool
pullbackCId :: SNatI n => PullbackCId n
pullbackCId cn = pullbackC idPhi cn == cn

type PullbackCComp n m l = Phi n m -> Phi m l -> C l -> Bool
pullbackCComp :: (SNatI n, SNatI m, SNatI l) => PullbackCComp n m l
pullbackCComp phiNM phiML cl =
  pullbackC (compPhi phiNM phiML) cl ==
    (pullbackC phiNM . pullbackC phiML) cl

-- pullbackC is linear
type PullbackCAdd n m = Phi n m -> C m -> C m -> Bool
pullbackCAdd :: (SNatI n, SNatI m) => PullbackCAdd n m
pullbackCAdd phi cm1 cm2 =
  pullbackC phi (cm1 <> cm2) == pullbackC phi cm1 <> pullbackC phi cm2

type PullbackCMult n m = Phi n m -> Rational -> R n -> C m -> Bool
pullbackCMult :: (SNatI n, SNatI m) => PullbackCMult n m
pullbackCMult phi r rn cm =
  (amult r . pullbackC phi) cm == (pullbackC phi . amult r) cm


-- pullbackD is a functor
type PullbackDId p n = Vec p (V n) -> D p n -> Bool
pullbackDId :: SNatI n => PullbackDId p n
pullbackDId vs dn = evalD vs (pullbackD idPhi dn) == evalD vs dn

type PullbackDComp p n m l = Phi n m -> Phi m l -> Vec p (V n) -> D p l -> Bool
pullbackDComp :: (SNatI n, SNatI m, SNatI l) => PullbackDComp p n m l
pullbackDComp phiNM phiML vs dl =
  evalD vs (pullbackD (compPhi phiNM phiML) dl) ==
    evalD vs (pullbackD phiNM . pullbackD phiML $ dl)

-- pullback is linear
type PullbackDAdd p n m = Phi n m -> Vec p (V n) -> D p m -> D p m -> Bool
pullbackDAdd :: (SNatI n, SNatI m) => PullbackDAdd p n m
pullbackDAdd phi vs dm1 dm2 =
  evalD vs (pullbackD phi $ dm1 <> dm2) ==
    evalD vs (pullbackD phi dm1 <> pullbackD phi dm2)

type PullbackDMult p n m = Phi n m -> C m -> Vec p (V n) -> D p m -> Bool
pullbackDMult :: (SNatI n, SNatI m) => PullbackDMult p n m
pullbackDMult phi cm vs dm =
  evalD vs (mmult (pullbackC phi cm) . pullbackD phi $ dm) ==
    evalD vs (pullbackD phi . mmult cm $ dm)


--pusforward
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
main = hspec $ do
  describe "Tests for Phi, PullbackC:" $ do
    prop "pullbackC works as expected for functions"
      (pullbackDefC :: PullbackDefC N.Nat3 N.Nat2)
    prop "pullbackC preserves identity"
      (pullbackCId :: PullbackCId N.Nat3)
    prop "pullbackC preserves composition"
      (pullbackCComp :: PullbackCComp N.Nat1 N.Nat2 N.Nat2)
    prop "pullbackC is preserves multiplication"
      (pullbackCMult :: PullbackCMult N.Nat3 N.Nat2)
    prop "pullbackC is preserves addition"
      (pullbackCAdd :: PullbackCAdd N.Nat2 N.Nat3)

  describe "Tests for Phi, PullbackD:" $ do
    prop "pullbackD preserves identity"
      (pullbackDId :: PullbackDId N.Nat2 N.Nat3)
    prop "pullbackD preserves composition"
      (pullbackDComp :: PullbackDComp N.Nat1 N.Nat1 N.Nat1 N.Nat1)
    prop "pullbackD is preserves multiplication"
      (pullbackDMult :: PullbackDMult N.Nat1 N.Nat1 N.Nat2)
    prop "pullbackD is preserves addition"
      (pullbackDAdd :: PullbackDAdd N.Nat1 N.Nat2 N.Nat3)



  describe "Tests for Phi, Pushforward:" $ do
    prop "pushforward works as expected"
      (pushforwardDef :: PushforwardDef N.Nat3 N.Nat2)
    prop "pushforward preserves identity"
      (pushforwardId :: PushforwardId N.Nat3)
    prop "pushforward preserves composition"
      (pushforwardComp :: PushforwardComp N.Nat1 N.Nat2 N.Nat2)
    prop "pushforward is preserves multiplication"
      (pushforwardMult :: PushforwardMult N.Nat3 N.Nat2)
    prop "pushforward is preserves addition"
      (pushforwardAdd :: PushforwardAdd N.Nat2 N.Nat3)

-- rename for exporting
mainPhi = main

