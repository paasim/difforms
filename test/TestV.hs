module TestV ( mainV ) where

import qualified Data.Type.Nat as N
import Data.Vec.Lazy ( Vec(..) )
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.List.NonEmpty ( NonEmpty(..) )
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import TestHelpers

-- Nothing to test with variables

-- V
type OneV n   = V n -> Bool
type TwoV n   = V n -> OneV n
type ThreeV n = V n -> TwoV n

type SemigroupSymmetricV n = C n -> TwoV n
semigroupSymmetricV :: N.SNatI n => SemigroupSymmetricV n
semigroupSymmetricV c v1 v2 = evalV c (v1 <> v2) == evalV c (v2 <> v1)

type SemigroupAssociatesV n = C n -> ThreeV n
semigroupAssociatesV :: N.SNatI n => SemigroupAssociatesV n
semigroupAssociatesV c v1 v2 v3 =
  evalV c ((v1 <> v2) <> v3) == evalV c (v1 <> (v2 <> v3))

type MonoidLeftIdV n = C n -> OneV n
monoidLeftIdV :: N.SNatI n => MonoidLeftIdV n
monoidLeftIdV c v = evalV c (mempty <> v) == evalV c v

type GroupInvV n = C n -> OneV n
groupInvV :: N.SNatI n => GroupInvV n
groupInvV c v = evalV c v <> evalV c (ginv v) == evalV c mempty
             && evalV c (ginv v) <> evalV c v == evalV c mempty

type ModuleAddDistributes1V n = C n -> C n -> C n -> OneV n
moduleAddDistributes1V :: N.SNatI n => ModuleAddDistributes1V n
moduleAddDistributes1V c1 c2 c v =
  evalV c (vmult c1 v <> vmult c2 v) == evalV c (vmult (c1 <> c2) v)

type ModuleAddDistributes2V n = C n -> C n -> TwoV n
moduleAddDistributes2V :: N.SNatI n => ModuleAddDistributes2V n
moduleAddDistributes2V c' c v1 v2 =
  evalV c (vmult c' v1 <> vmult c' v2) == evalV c (vmult c' (v1 <> v2))

type ModuleMultAssociatesV n = C n -> C n -> C n -> OneV n
moduleMultAssociatesV :: N.SNatI n => ModuleMultAssociatesV n
moduleMultAssociatesV c1 c2 c v =
  evalV c (vmult c1 (vmult c2 v)) == evalV c (vmult (c1 `sappend` c2) v)

type Module1IdV n = C n -> OneV n
module1IdV :: N.SNatI n => Module1IdV n
module1IdV c v = evalV c (vmult sempty v) == evalV c v

type LinearAddV n = C n -> C n -> OneV n
linearAddV :: N.SNatI n => LinearAddV n
linearAddV c1 c2 v = evalV (c1 <> c2) v == evalV c1 v <> evalV c2 v

type LinearMultV n = Rational -> C n -> OneV n
linearMultV :: N.SNatI n => LinearMultV n
linearMultV d c v = evalV (amult d c) v == amult d (evalV c v)

type LeibnizRuleV n =  C n -> C n -> OneV n
leibnizRuleV :: N.SNatI n => LeibnizRuleV n
leibnizRuleV c1 c2 v =
  evalV (c1 `sappend` c2) v == (evalV c1 v `sappend` c2) <>
                                 (c1 `sappend` evalV c2 v)

-- Vp
type OneVp n   = Vec n Rational -> R n -> Bool
type TwoVp n   = Vec n Rational -> OneVp n
type ThreeVp n = Vec n Rational -> TwoVp n

type SemigroupSymmetricVp n = C n -> TwoVp n
semigroupSymmetricVp :: N.SNatI n => SemigroupSymmetricVp n
semigroupSymmetricVp c v1 v2 p = let vp1 = Vp p v1
                                     vp2 = Vp p v2
  in fmap (evalVp c) (vpappend vp1 vp2)
    == fmap (evalVp c) (vpappend vp2 vp1)

type SemigroupAssociatesVp n = C n -> ThreeVp n
semigroupAssociatesVp :: N.SNatI n => SemigroupAssociatesVp n
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

type ModuleAddDistributes1Vp n = Rational -> Rational -> C n -> OneVp n
moduleAddDistributes1Vp :: N.SNatI n => ModuleAddDistributes1Vp n
moduleAddDistributes1Vp d1 d2 c v p = let vp = Vp p v
  in fmap (evalVp c) (vpappend (vpmult d1 vp) (vpmult d2 vp))
    == Just (evalVp c $ vpmult (d1 + d2) vp)

type ModuleAddDistributes2Vp n = Rational -> C n -> TwoVp n
moduleAddDistributes2Vp :: N.SNatI n => ModuleAddDistributes2Vp n
moduleAddDistributes2Vp d c v1 v2 p = let vp1 = Vp p v1
                                          vp2 = Vp p v2
  in fmap (evalVp c) (vpappend (vpmult d vp1) (vpmult d vp2))
    == fmap (evalVp c . vpmult d) (vpappend vp1 vp2)

type ModuleMultAssociatesVp n = Rational -> Rational -> C n -> OneVp n
moduleMultAssociatesVp :: N.SNatI n => ModuleMultAssociatesVp n
moduleMultAssociatesVp d1 d2 c v p = let vp = Vp p v
  in evalVp c (vpmult d1 (vpmult d2 vp)) == evalVp c (vpmult (d1 * d2) vp)

type Module1IdVp n = C n -> OneVp n
module1IdVp :: N.SNatI n => Module1IdVp n
module1IdVp c v p = let vp = Vp p v
  in evalVp c (vpmult 1 vp) == evalVp c vp

type LinearAddVp n = C n -> C n -> OneVp n
linearAddVp :: N.SNatI n => LinearAddVp n
linearAddVp c1 c2 v p = let vp = Vp p v
  in evalVp (c1 <> c2) vp == evalVp c1 vp + evalVp c2 vp

type LinearMultVp n = Rational -> C n -> OneVp n
linearMultVp :: N.SNatI n => LinearMultVp n
linearMultVp d c v p = let vp = Vp p v
  in evalVp (amult d c) vp == d * evalVp c vp

type LeibnizRuleVp n =  C n -> C n -> OneVp n
leibnizRuleVp :: N.SNatI n => LeibnizRuleVp n
leibnizRuleVp c1 c2 v p = let vp = Vp p v
  in evalVp (c1 `sappend` c2) vp == (evalVp c1 vp * evalC p c2) +
                                        (evalC p c1 * evalVp c2 vp)


main :: IO ()
main = do
  putStrLn "Tests for V:"
  qc "semigroup symmetric"
    (semigroupSymmetricV :: SemigroupSymmetricV N.Nat3)
  qc "semigroup associative"
    (semigroupAssociatesV :: SemigroupAssociatesV N.Nat3)
  qc "monoid left identity"
    (monoidLeftIdV :: MonoidLeftIdV N.Nat3)
  qc "group has inverses"
    (groupInvV :: GroupInvV N.Nat3)
  qc "module ring addition distributive"
    (moduleAddDistributes1V :: ModuleAddDistributes1V N.Nat3)
  qc "module group addition distributive"
    (moduleAddDistributes2V :: ModuleAddDistributes2V N.Nat3)
  qc "module multiplication associative"
    (moduleMultAssociatesV :: ModuleMultAssociatesV N.Nat3)
  qc "module multiplication by 1 is identity"
    (module1IdV :: Module1IdV N.Nat3)
  qc "addition linear"
    (linearAddV :: LinearAddV N.Nat3)
  qc "multiplication by rationals linear"
    (linearMultV :: LinearMultV N.Nat3)
  qc "Leibniz rule"
    (leibnizRuleV :: LeibnizRuleV N.Nat3)

  putStrLn "Tests for Vp:"
  qc "semigroup symmetric"
    (semigroupSymmetricVp :: SemigroupSymmetricVp N.Nat3)
  qc "semigroup associative"
    (semigroupAssociatesVp :: SemigroupAssociatesVp N.Nat3)
--  qc "monoid left identity"
--    (monoidLeftIdVp :: MonoidLeftIdVp N.Nat3)
--  qc "group has inverses"
--    (groupInvVp :: GroupInvVp N.Nat3)
  qc "module ring addition distributive"
    (moduleAddDistributes1Vp :: ModuleAddDistributes1Vp N.Nat3)
  qc "module group addition distributive"
    (moduleAddDistributes2Vp :: ModuleAddDistributes2Vp N.Nat3)
  qc "module multiplication associative"
    (moduleMultAssociatesVp :: ModuleMultAssociatesVp N.Nat3)
  qc "module multiplication by 1 is identity"
    (module1IdVp :: Module1IdVp N.Nat3)
  qc "addition linear"
    (linearAddVp :: LinearAddVp N.Nat3)
  qc "multiplication by rationals linear"
    (linearMultVp :: LinearMultVp N.Nat3)
  qc "Leibniz rule"
    (leibnizRuleVp :: LeibnizRuleVp N.Nat3)



-- rename for exporting
mainV = main

