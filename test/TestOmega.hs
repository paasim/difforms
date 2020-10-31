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


-- rename for exporting
mainOmega = main

