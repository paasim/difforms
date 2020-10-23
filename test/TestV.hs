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
semigroupSymmetricV ts v1 v2 = evalV (v1 <> v2) ts == evalV (v2 <> v1) ts

type SemigroupAssociatesV n = C n -> ThreeV n
semigroupAssociatesV :: N.SNatI n => SemigroupAssociatesV n
semigroupAssociatesV ts v1 v2 v3 =
  evalV ((v1 <> v2) <> v3) ts == evalV (v1 <> (v2 <> v3)) ts

type MonoidLeftIdV n = C n -> OneV n
monoidLeftIdV :: N.SNatI n => MonoidLeftIdV n
monoidLeftIdV ts v = evalV (mempty <> v) ts == evalV v ts

type GroupInvV n = C n -> OneV n
groupInvV :: N.SNatI n => GroupInvV n
groupInvV ts v = evalV v ts <> evalV (ginv v) ts == evalV mempty ts
             && evalV (ginv v) ts <> evalV v ts == evalV mempty ts

type ModuleAddDistributes1V n = C n -> C n -> C n -> OneV n
moduleAddDistributes1V :: N.SNatI n => ModuleAddDistributes1V n
moduleAddDistributes1V ts1 ts2 ts v =
  evalV (vmult ts1 v <> vmult ts2 v) ts == evalV (vmult (ts1 <> ts2) v) ts

type ModuleAddDistributes2V n = C n -> C n -> TwoV n
moduleAddDistributes2V :: N.SNatI n => ModuleAddDistributes2V n
moduleAddDistributes2V ts' ts v1 v2 =
  evalV (vmult ts' v1 <> vmult ts' v2) ts == evalV (vmult ts' (v1 <> v2)) ts

type ModuleMultAssociatesV n = C n -> C n -> C n -> OneV n
moduleMultAssociatesV :: N.SNatI n => ModuleMultAssociatesV n
moduleMultAssociatesV ts1 ts2 ts v =
  evalV (vmult ts1 (vmult ts2 v)) ts == evalV (vmult (ts1 `sappend` ts2) v) ts

type Module1IdV n = C n -> OneV n
module1IdV :: N.SNatI n => Module1IdV n
module1IdV ts v = evalV (vmult sempty v) ts == evalV v ts

type LinearAddV n = C n -> C n -> OneV n
linearAddV :: N.SNatI n => LinearAddV n
linearAddV ts1 ts2 v = evalV v (ts1 <> ts2) == evalV v ts1 <> evalV v ts2

type LinearMultV n = Rational -> C n -> OneV n
linearMultV :: N.SNatI n => LinearMultV n
linearMultV r ts v = evalV v (amult r ts) == amult r (evalV v ts)

type LeibnizRuleV n =  C n -> C n -> OneV n
leibnizRuleV :: N.SNatI n => LeibnizRuleV n
leibnizRuleV ts1 ts2 v =
  evalV v (ts1 `sappend` ts2) == (evalV v ts1 `sappend` ts2) <>
                                 (ts1 `sappend` evalV v ts2)

-- Vp
type OneVp n   = Vec n Rational -> R n -> Bool
type TwoVp n   = Vec n Rational -> OneVp n
type ThreeVp n = Vec n Rational -> TwoVp n

type SemigroupSymmetricVp n = C n -> TwoVp n
semigroupSymmetricVp :: N.SNatI n => SemigroupSymmetricVp n
semigroupSymmetricVp ts v1 v2 p = let vp1 = Vp p v1
                                      vp2 = Vp p v2
  in fmap (\vp -> evalVp vp ts) (vpappend vp1 vp2)
    == fmap (\vp -> evalVp vp ts) (vpappend vp2 vp1)

type SemigroupAssociatesVp n = C n -> ThreeVp n
semigroupAssociatesVp :: N.SNatI n => SemigroupAssociatesVp n
semigroupAssociatesVp ts v1 v2 v3 p = let vp1 = Vp p v1
                                          vp2 = Vp p v2
                                          vp3 = Vp p v3
  in fmap (\vp -> evalVp vp ts) (vpappend vp1 vp2 >>= \vp -> vpappend vp vp3)
    == fmap (\vp -> evalVp vp ts) (vpappend vp2 vp3 >>= vpappend vp1)

{-
type MonoidLeftIdVp n = C n -> OneVp n
monoidLeftIdVp :: N.SNatI n => MonoidLeftIdVp n
monoidLeftIdVp ts v p = let vp = Vp p v
  in evalVp (mempty <> vp) ts == evalVp vp ts

type GroupInvVp n = C n -> OneVp n
groupInvVp :: N.SNatI n => GroupInvVp n
groupInvVp ts v p = let vp = Vp p v
  in evalVp vp ts <> evalVp (ginv vp) ts == evalVp mempty ts
    && evalVp (ginv vp) ts <> evalVp vp ts == evalVp mempty ts
-}

type ModuleAddDistributes1Vp n = Rational -> Rational -> C n -> OneVp n
moduleAddDistributes1Vp :: N.SNatI n => ModuleAddDistributes1Vp n
moduleAddDistributes1Vp d1 d2 ts v p = let vp = Vp p v
  in fmap (\vp -> evalVp vp ts) (vpappend (vpmult d1 vp) (vpmult d2 vp))
    == Just (evalVp (vpmult (d1 + d2) vp) ts)

type ModuleAddDistributes2Vp n = Rational -> C n -> TwoVp n
moduleAddDistributes2Vp :: N.SNatI n => ModuleAddDistributes2Vp n
moduleAddDistributes2Vp ts' ts v1 v2 p = let vp1 = Vp p v1
                                             vp2 = Vp p v2
  in fmap (\vp -> evalVp vp ts) (vpappend (vpmult ts' vp1) (vpmult ts' vp2))
    == fmap (\vp -> evalVp (vpmult ts' vp) ts) (vpappend vp1 vp2)

type ModuleMultAssociatesVp n = Rational -> Rational -> C n -> OneVp n
moduleMultAssociatesVp :: N.SNatI n => ModuleMultAssociatesVp n
moduleMultAssociatesVp d1 d2 ts v p = let vp = Vp p v
  in evalVp (vpmult d1 (vpmult d2 vp)) ts == evalVp (vpmult (d1 * d2) vp) ts

type Module1IdVp n = C n -> OneVp n
module1IdVp :: N.SNatI n => Module1IdVp n
module1IdVp ts v p = let vp = Vp p v
  in evalVp (vpmult 1 vp) ts == evalVp vp ts

type LinearAddVp n = C n -> C n -> OneVp n
linearAddVp :: N.SNatI n => LinearAddVp n
linearAddVp ts1 ts2 v p = let vp = Vp p v
  in evalVp vp (ts1 <> ts2) == evalVp vp ts1 + evalVp vp ts2

type LinearMultVp n = Rational -> C n -> OneVp n
linearMultVp :: N.SNatI n => LinearMultVp n
linearMultVp r ts v p = let vp = Vp p v
  in evalVp vp (amult r ts) == r * evalVp vp ts

type LeibnizRuleVp n =  C n -> C n -> OneVp n
leibnizRuleVp :: N.SNatI n => LeibnizRuleVp n
leibnizRuleVp ts1 ts2 v p = let vp = Vp p v
  in evalVp vp (ts1 `sappend` ts2) == (evalVp vp ts1 * evalTerms ts2 p) +
                                        (evalTerms ts1 p * evalVp vp ts2)


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

