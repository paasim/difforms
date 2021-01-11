module TestV ( testV ) where

import Data.Type.Nat ( SNatI )
import qualified Data.Type.Nat as N
import Data.Vec.Lazy ( Vec(..) )
import Test.Hspec
import Test.Hspec.QuickCheck
import Common
import C
import V

-- V
type OneV n   = V n -> Bool
type TwoV n   = V n -> OneV n
type ThreeV n = V n -> TwoV n

type SemigroupSymmetricV n = C n -> TwoV n
semigroupSymmetricV :: SNatI n => SemigroupSymmetricV n
semigroupSymmetricV c v1 v2 = evalV c (v1 <> v2) == evalV c (v2 <> v1)

type SemigroupAssociatesV n = C n -> ThreeV n
semigroupAssociatesV :: SNatI n => SemigroupAssociatesV n
semigroupAssociatesV c v1 v2 v3 =
  evalV c ((v1 <> v2) <> v3) == evalV c (v1 <> (v2 <> v3))

type MonoidLeftIdV n = C n -> OneV n
monoidLeftIdV :: SNatI n => MonoidLeftIdV n
monoidLeftIdV c v = evalV c (mempty <> v) == evalV c v

type GroupInvV n = C n -> OneV n
groupInvV :: SNatI n => GroupInvV n
groupInvV c v = evalV c v <> evalV c (ginv v) == evalV c mempty
             && evalV c (ginv v) <> evalV c v == evalV c mempty

type ModuleAddDistributes1V n = C n -> C n -> C n -> OneV n
moduleAddDistributes1V :: SNatI n => ModuleAddDistributes1V n
moduleAddDistributes1V c1 c2 c v =
  evalV c (mmult c1 v <> mmult c2 v) == evalV c (mmult (c1 <> c2) v)

type ModuleAddDistributes2V n = C n -> C n -> TwoV n
moduleAddDistributes2V :: SNatI n => ModuleAddDistributes2V n
moduleAddDistributes2V c' c v1 v2 =
  evalV c (mmult c' v1 <> mmult c' v2) == evalV c (mmult c' (v1 <> v2))

type ModuleMultAssociatesV n = C n -> C n -> C n -> OneV n
moduleMultAssociatesV :: SNatI n => ModuleMultAssociatesV n
moduleMultAssociatesV c1 c2 c v =
  evalV c (mmult c1 (mmult c2 v)) == evalV c (mmult (c1 `sappend` c2) v)

type Module1IdV n = C n -> OneV n
module1IdV :: SNatI n => Module1IdV n
module1IdV c v = evalV c (mmult sempty v) == evalV c v

type LinearAddV n = C n -> C n -> OneV n
linearAddV :: SNatI n => LinearAddV n
linearAddV c1 c2 v = evalV (c1 <> c2) v == evalV c1 v <> evalV c2 v

type LinearMultV n = Number -> C n -> OneV n
linearMultV :: SNatI n => LinearMultV n
linearMultV d c v = evalV (amult d c) v == amult d (evalV c v)

type LeibnizRuleV n =  C n -> C n -> OneV n
leibnizRuleV :: SNatI n => LeibnizRuleV n
leibnizRuleV c1 c2 v =
  evalV (c1 `sappend` c2) v == (evalV c1 v `sappend` c2) <>
                                 (c1 `sappend` evalV c2 v)


type LieBracketDef n = C n -> TwoV n
lieBracketDef :: SNatI n => LieBracketDef n
lieBracketDef c v w =
  evalV c (lieBracket v w) == evalV (evalV c w) v <> ginv (evalV (evalV c v) w)

type LieBracketLeibniz n = C n -> C n -> TwoV n
lieBracketLeibniz :: SNatI n => LieBracketLeibniz n
lieBracketLeibniz c1 c2 v w = let vw = lieBracket v w
  in evalV (c1 `sappend` c2) vw == (evalV c1 vw `sappend` c2) <>
                                   (c1 `sappend` evalV c2 vw)

type LieBracketAntisymmetric n = C n -> TwoV n
lieBracketAntisymmetric :: SNatI n => LieBracketAntisymmetric n
lieBracketAntisymmetric c v w =
  evalV c (lieBracket v w) == ginv (evalV c (lieBracket w v))

type LieBracketBilinear1 n = Number -> Number -> C n -> ThreeV n
lieBracketBilinear1 :: SNatI n => LieBracketBilinear1 n
lieBracketBilinear1 r1 r2 c v u w =
  let r1u = mmult (amult r1 sempty) u
      r2v = mmult (amult r2 sempty) v
      r1uw = mmult (amult r1 sempty) (lieBracket u w)
      r2vw = mmult (amult r2 sempty) (lieBracket v w)
  in evalV c (lieBracket (r1u <> r2v) w) == evalV c (r1uw <> r2vw)

type LieBracketBilinear2 n = Number -> Number -> C n -> ThreeV n
lieBracketBilinear2 :: SNatI n => LieBracketBilinear2 n
lieBracketBilinear2 r1 r2 c u v w =
  let r1v = mmult (amult r1 sempty) v
      r2w = mmult (amult r2 sempty) w
      r1uv = mmult (amult r1 sempty) (lieBracket u v)
      r2uw = mmult (amult r2 sempty) (lieBracket u w)
  in evalV c (lieBracket u (r1v <> r2w)) == evalV c (r1uv <> r2uw)

type LieBracketJacobi n = C n -> ThreeV n
lieBracketJacobi :: SNatI n => LieBracketJacobi n
lieBracketJacobi c u v w =
  let uvw = lieBracket u $ lieBracket v w
      vwu = lieBracket v $ lieBracket w u
      wuv = lieBracket w $ lieBracket u v
  in evalV c (uvw <> vwu <> wuv) == evalV c mempty


-- Vp
type OneVp n   = Vec n Number -> Vec n Number -> Bool
type TwoVp n   = Vec n Number -> OneVp n
type ThreeVp n = Vec n Number -> TwoVp n

type SemigroupSymmetricVp n = C n -> TwoVp n
semigroupSymmetricVp :: SNatI n => SemigroupSymmetricVp n
semigroupSymmetricVp c v1 v2 p = let vp1 = Vp p v1
                                     vp2 = Vp p v2
  in fmap (evalVp c) (vpappend vp1 vp2)
    == fmap (evalVp c) (vpappend vp2 vp1)

type SemigroupAssociatesVp n = C n -> ThreeVp n
semigroupAssociatesVp :: SNatI n => SemigroupAssociatesVp n
semigroupAssociatesVp c v1 v2 v3 p = let vp1 = Vp p v1
                                         vp2 = Vp p v2
                                         vp3 = Vp p v3
  in fmap (evalVp c) (vpappend vp1 vp2 >>= \vp -> vpappend vp vp3)
    == fmap (evalVp c) (vpappend vp2 vp3 >>= vpappend vp1)

{-
type MonoidLeftIdVp n = C n -> OneVp n
monoidLeftIdVp :: N.SNatI n => MonoidLeftIdVp n
monoidLeftIdVp c v p = let vp = Vp p v
  in evalVp c (mempty <> vp) == evalVp c vp

type GroupInvVp n = C n -> OneVp n
groupInvVp :: N.SNatI n => GroupInvVp n
groupInvVp c v p = let vp = Vp p v
  in evalVp c vp <> evalVp c (ginv vp) == evalVp c mempty
    && evalVp c (ginv vp) <> evalVp c vp == evalVp c mempty
-}

type ModuleAddDistributes1Vp n = Number -> Number -> C n -> OneVp n
moduleAddDistributes1Vp :: SNatI n => ModuleAddDistributes1Vp n
moduleAddDistributes1Vp d1 d2 c v p = let vp = Vp p v
  in fmap (evalVp c) (vpappend (vpmult d1 vp) (vpmult d2 vp))
    == Just (evalVp c $ vpmult (d1 + d2) vp)

type ModuleAddDistributes2Vp n = Number -> C n -> TwoVp n
moduleAddDistributes2Vp :: SNatI n => ModuleAddDistributes2Vp n
moduleAddDistributes2Vp d c v1 v2 p = let vp1 = Vp p v1
                                          vp2 = Vp p v2
  in fmap (evalVp c) (vpappend (vpmult d vp1) (vpmult d vp2))
    == fmap (evalVp c . vpmult d) (vpappend vp1 vp2)

type ModuleMultAssociatesVp n = Number -> Number -> C n -> OneVp n
moduleMultAssociatesVp :: SNatI n => ModuleMultAssociatesVp n
moduleMultAssociatesVp d1 d2 c v p = let vp = Vp p v
  in evalVp c (vpmult d1 (vpmult d2 vp)) == evalVp c (vpmult (d1 * d2) vp)

type Module1IdVp n = C n -> OneVp n
module1IdVp :: SNatI n => Module1IdVp n
module1IdVp c v p = let vp = Vp p v
  in evalVp c (vpmult 1 vp) == evalVp c vp

type LinearAddVp n = C n -> C n -> OneVp n
linearAddVp :: SNatI n => LinearAddVp n
linearAddVp c1 c2 v p = let vp = Vp p v
  in evalVp (c1 <> c2) vp == evalVp c1 vp + evalVp c2 vp

type LinearMultVp n = Number -> C n -> OneVp n
linearMultVp :: SNatI n => LinearMultVp n
linearMultVp d c v p = let vp = Vp p v
  in evalVp (amult d c) vp == d * evalVp c vp

type LeibnizRuleVp n =  C n -> C n -> OneVp n
leibnizRuleVp :: SNatI n => LeibnizRuleVp n
leibnizRuleVp c1 c2 v p = let vp = Vp p v
  in evalVp (c1 `sappend` c2) vp == (evalVp c1 vp * evalC p c2) +
                                        (evalC p c1 * evalVp c2 vp)


testV :: IO ()
testV = hspec $ do
  describe "Tests for V, V:" $ do
    prop "semigroup symmetric"
      (semigroupSymmetricV :: SemigroupSymmetricV N.Nat3)
    prop "semigroup associative"
      (semigroupAssociatesV :: SemigroupAssociatesV N.Nat3)
    prop "monoid left identity"
      (monoidLeftIdV :: MonoidLeftIdV N.Nat3)
    prop "group has inverses"
      (groupInvV :: GroupInvV N.Nat3)
    prop "module ring addition distributive"
      (moduleAddDistributes1V :: ModuleAddDistributes1V N.Nat3)
    prop "module group addition distributive"
      (moduleAddDistributes2V :: ModuleAddDistributes2V N.Nat3)
    prop "module multiplication associative"
      (moduleMultAssociatesV :: ModuleMultAssociatesV N.Nat3)
    prop "module multiplication by 1 is identity"
      (module1IdV :: Module1IdV N.Nat3)
    prop "addition linear"
      (linearAddV :: LinearAddV N.Nat3)
    prop "multiplication by rationals linear"
      (linearMultV :: LinearMultV N.Nat3)
    prop "Leibniz rule"
      (leibnizRuleV :: LeibnizRuleV N.Nat3)

  describe "Tests for V, Lie bracket:" $ do
    prop "Lie bracket satisfies the definition"
      (lieBracketDef :: LieBracketDef N.Nat3)
    prop "Lie bracket satisfies the leibniz rule"
      (lieBracketLeibniz :: LieBracketLeibniz N.Nat3)
    prop "Lie bracket antisymmetric"
      (lieBracketAntisymmetric :: LieBracketAntisymmetric N.Nat3)
    prop "Lie bracket linear in the first argument"
      (lieBracketBilinear1 :: LieBracketBilinear1 N.Nat3)
    prop "Lie bracket linear in the second argument"
      (lieBracketBilinear2 :: LieBracketBilinear2 N.Nat3)
    prop "Lie bracket satisfies jacobi identity"
      (lieBracketJacobi :: LieBracketJacobi N.Nat3)

  describe "Tests for V, Vp:" $ do
    prop "semigroup symmetric"
      (semigroupSymmetricVp :: SemigroupSymmetricVp N.Nat3)
    prop "semigroup associative"
      (semigroupAssociatesVp :: SemigroupAssociatesVp N.Nat3)
--    prop "monoid left identity"
--      (monoidLeftIdVp :: MonoidLeftIdVp N.Nat3)
--    prop "group has inverses"
--      (groupInvVp :: GroupInvVp N.Nat3)
    prop "module ring addition distributive"
      (moduleAddDistributes1Vp :: ModuleAddDistributes1Vp N.Nat3)
    prop "module group addition distributive"
      (moduleAddDistributes2Vp :: ModuleAddDistributes2Vp N.Nat3)
    prop "module multiplication associative"
      (moduleMultAssociatesVp :: ModuleMultAssociatesVp N.Nat3)
    prop "module multiplication by 1 is identity"
      (module1IdVp :: Module1IdVp N.Nat3)
    prop "addition linear"
      (linearAddVp :: LinearAddVp N.Nat3)
    prop "multiplication by rationals linear"
      (linearMultVp :: LinearMultVp N.Nat3)
    prop "Leibniz rule"
      (leibnizRuleVp :: LeibnizRuleVp N.Nat3)

