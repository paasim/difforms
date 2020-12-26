module TestOmega ( mainOmega ) where

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
import Omega
import TestHelpers

-- Omega
type OneO n   = Omega n -> Bool
type TwoO n   = Omega n -> OneO n
type ThreeO n = Omega n -> TwoO n

type SemigroupSymmetricO n = Vec n (V n) -> TwoO n
semigroupSymmetricO :: N.SNatI n => SemigroupSymmetricO n
semigroupSymmetricO vs o1 o2 =
  evalOmega vs (o1 <> o2) == evalOmega vs (o2 <> o1)

type SemigroupAssociatesO n = Vec n (V n) -> ThreeO n
semigroupAssociatesO :: N.SNatI n => SemigroupAssociatesO n
semigroupAssociatesO vs o1 o2 o3 =
  evalOmega vs ((o1 <> o2) <> o3) == evalOmega vs (o1 <> (o2 <> o3))

type MonoidLeftIdO n = Vec n (V n) -> OneO n
monoidLeftIdO :: N.SNatI n => MonoidLeftIdO n
monoidLeftIdO vs o = evalOmega vs (mempty <> o) == evalOmega vs o

type GroupInvO n = Vec n (V n) -> OneO n
groupInvO :: N.SNatI n => GroupInvO n
groupInvO vs o =
  evalOmega vs o <> evalOmega vs (ginv o) == evalOmega vs mempty
   && evalOmega vs (ginv o) <> evalOmega vs o == evalOmega vs mempty

type ModuleAddDistributes1O n = C n -> C n -> Vec n (V n) -> OneO n
moduleAddDistributes1O :: N.SNatI n => ModuleAddDistributes1O n
moduleAddDistributes1O c1 c2 vs o =
  evalOmega vs (mmult c1 o <> mmult c2 o) == evalOmega vs (mmult (c1 <> c2) o)

type ModuleAddDistributes2O n = C n -> Vec n (V n) -> TwoO n
moduleAddDistributes2O :: N.SNatI n => ModuleAddDistributes2O n
moduleAddDistributes2O c vs o1 o2 =
  evalOmega vs (mmult c o1 <> mmult c o2) == evalOmega vs (mmult c (o1 <> o2))

type ModuleMultAssociatesO n = C n -> C n -> Vec n (V n) -> OneO n
moduleMultAssociatesO :: N.SNatI n => ModuleMultAssociatesO n
moduleMultAssociatesO c1 c2 vs o =
  evalOmega vs (mmult c1 (mmult c2 o)) == evalOmega vs (mmult (c1 `sappend` c2) o)

type Module1IdO n = Vec n (V n) -> OneO n
module1IdO :: N.SNatI n => Module1IdO n
module1IdO vs o = evalOmega vs (mmult sempty o) == evalOmega vs o

type LinearAddO n = Vec n (V n) -> TwoO n
linearAddO :: N.SNatI n => LinearAddO n
linearAddO vs o1 o2 = evalOmega vs (o1 <> o2) == evalOmega vs o1 <> evalOmega vs o2

type LinearMultO n = C n -> Vec n (V n) -> OneO n
linearMultO :: N.SNatI n => LinearMultO n
linearMultO c vs o = evalOmega vs (mmult c o) == sappend c (evalOmega vs o)


type D0LinearAdd n = Vec n (V n) -> C n -> C n -> Bool
d0LinearAdd :: N.SNatI n => D0LinearAdd n
d0LinearAdd v c1 c2 =
  evalOmega v (d0 c1 <> d0 c2) == evalOmega v (d0 $ c1 <> c2)

type D0LinearMult n = Rational -> Vec n (V n) -> C n -> Bool
d0LinearMult :: N.SNatI n => D0LinearMult n
d0LinearMult r v c =
  evalOmega v (d0 $ amult r c)
    == evalOmega v (mmult (liftToC . liftToTerm $ r) $ d0 c)

type D0LeibnizRule n = Vec n (V n) -> C n -> C n -> Bool
d0LeibnizRule :: N.SNatI n => D0LeibnizRule n
d0LeibnizRule v c1 c2 =
  evalOmega v (d0 $ sappend c1 c2)
    == evalOmega v (mmult c1 (d0 c2) <> mmult c2 (d0 c1))


type DLinearAdd n = Vec n (V n) -> Omega n -> Omega n -> Bool
dLinearAdd :: N.SNatI n => DLinearAdd n
dLinearAdd vs o1 o2 =
  evalOmega vs (d $ o1 <> o2) == evalOmega vs (d o1) <> evalOmega vs (d o2)

type DLinearMult n = Rational -> Vec n (V n) -> Omega n -> Bool
dLinearMult :: N.SNatI n => DLinearMult n
dLinearMult r vs o =
  evalOmega vs (d $ mmult (liftToC . liftToTerm $ r) o)
    == evalOmega vs (mmult (liftToC . liftToTerm $ r) $ d o)

-- leibniz rule applies only when the first argument of the exterior
-- product is a p-form

type DTwiceZero n = Vec n (V n) -> Omega n -> Bool
dTwiceZero :: N.SNatI n => DTwiceZero n
dTwiceZero vs o = evalOmega vs (d . d $ o) == mempty


main :: IO ()
main = do
  putStrLn "Tests for Omega:"
  qc "semigroup symmetric"
    (semigroupSymmetricO :: SemigroupSymmetricO N.Nat3)
  qc "semigroup associative"
    (semigroupAssociatesO :: SemigroupAssociatesO N.Nat3)
  qc "monoid left identity"
    (monoidLeftIdO :: MonoidLeftIdO N.Nat3)
  qc "group has inverses"
    (groupInvO :: GroupInvO N.Nat3)
  qc "module ring addition distributive"
    (moduleAddDistributes1O :: ModuleAddDistributes1O N.Nat3)
  qc "module group addition distributive"
    (moduleAddDistributes2O :: ModuleAddDistributes2O N.Nat3)
  qc "module multiplication associative"
    (moduleMultAssociatesO :: ModuleMultAssociatesO N.Nat3)
  qc "module multiplication by 1 is identity"
    (module1IdO :: Module1IdO N.Nat3)
  qc "addition linear"
    (linearAddO :: LinearAddO N.Nat3)
  qc "multiplication by C n linear"
    (linearMultO :: LinearMultO N.Nat3)

  putStrLn "Tests for d0:"
  qc "addition linear"
    (d0LinearAdd :: D0LinearAdd N.Nat3)
  qc "multiplication linear"
    (d0LinearMult :: D0LinearMult N.Nat3)
  qc "leibniz rule"
    (d0LeibnizRule :: D0LeibnizRule N.Nat3)

  putStrLn "Tests for d:"
  qc "addition linear"
    (dLinearAdd :: DLinearAdd N.Nat3)
  qc "multiplication linear"
    (dLinearMult :: DLinearMult N.Nat3)
  qc "dd = 0"
    (dTwiceZero :: DTwiceZero N.Nat3)


-- rename for exporting
mainOmega = main

