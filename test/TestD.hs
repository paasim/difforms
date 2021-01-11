{-# LANGUAGE DataKinds #-}
module TestD ( testD ) where

import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Vec.Lazy ( Vec(..) )
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Common
import C
import V
import D

-- D
type OneD p n   = D p n -> Bool
type TwoD p n   = D p n -> OneD p n
type ThreeD p n = D p n -> TwoD p n

type SemigroupSymmetricD p n = Vec p (V n) -> TwoD p n
semigroupSymmetricD :: N.SNatI n => SemigroupSymmetricD (S p) n
semigroupSymmetricD vs d1 d2 =
  evalD vs (d1 <> d2) == evalD vs (d2 <> d1)

type SemigroupAssociatesD p n = Vec p (V n) -> ThreeD p n
semigroupAssociatesD :: N.SNatI n => SemigroupAssociatesD (S p) n
semigroupAssociatesD vs d1 d2 d3 =
  evalD vs ((d1 <> d2) <> d3) == evalD vs (d1 <> (d2 <> d3))

type MonoidLeftIdD p n = Vec p (V n) -> OneD p n
monoidLeftIdD :: N.SNatI n => MonoidLeftIdD (S p) n
monoidLeftIdD vs d = evalD vs (mempty <> d) == evalD vs d

type GroupInvD p n = Vec p (V n) -> OneD p n
groupInvD :: N.SNatI n => GroupInvD (S p) n
groupInvD vs d =
  evalD vs d <> evalD vs (ginv d) == evalD vs mempty
   && evalD vs (ginv d) <> evalD vs d == evalD vs mempty

type ModuleAddDistributes1D p n = C n -> C n -> Vec p (V n) -> OneD p n
moduleAddDistributes1D :: N.SNatI n => ModuleAddDistributes1D (S p) n
moduleAddDistributes1D c1 c2 vs d =
  evalD vs (mmult c1 d <> mmult c2 d) == evalD vs (mmult (c1 <> c2) d)

type ModuleAddDistributes2D p n = C n -> Vec p (V n) -> TwoD p n
moduleAddDistributes2D :: N.SNatI n => ModuleAddDistributes2D (S p) n
moduleAddDistributes2D c vs d1 d2 =
  evalD vs (mmult c d1 <> mmult c d2) == evalD vs (mmult c (d1 <> d2))

type ModuleMultAssociatesD p n = C n -> C n -> Vec p (V n) -> OneD p n
moduleMultAssociatesD :: N.SNatI n => ModuleMultAssociatesD (S p) n
moduleMultAssociatesD c1 c2 vs d =
  evalD vs (mmult c1 (mmult c2 d)) == evalD vs (mmult (c1 `sappend` c2) d)

type Module1IdD p n = Vec p (V n) -> OneD p n
module1IdD :: N.SNatI n => Module1IdD (S p) n
module1IdD vs d = evalD vs (mmult sempty d) == evalD vs d

type LinearAddD p n = Vec p (V n) -> TwoD p n
linearAddD :: N.SNatI n => LinearAddD (S p) n
linearAddD vs d1 d2 = evalD vs (d1 <> d2) == evalD vs d1 <> evalD vs d2

type LinearMultD p n = C n -> Vec p (V n) -> OneD p n
linearMultD :: N.SNatI n => LinearMultD (S p) n
linearMultD c vs d = evalD vs (mmult c d) == sappend c (evalD vs d)

type ExtProdSuperComm p n = Vec (N.Plus p p) (V n) -> TwoD p n
extProdSuperComm :: Number -> ExtProdSuperComm (S p) n
extProdSuperComm r vs d1 d2 =
  let p = exteriorProduct d1 d2
      pFlip = exteriorProduct d2 d1
      pFlipSign = mmult (liftToC . liftToTerm $ r) pFlip
  in evalD vs p == evalD vs pFlipSign


type D0LinearAdd n = Vec N.Nat1 (V n) -> C n -> C n -> Bool
d0LinearAdd :: N.SNatI n => D0LinearAdd n
d0LinearAdd v c1 c2 =
  evalD v (d0 c1 <> d0 c2) == evalD v (d0 $ c1 <> c2)

type D0LinearMult n = Number -> Vec N.Nat1 (V n) -> C n -> Bool
d0LinearMult :: N.SNatI n => D0LinearMult n
d0LinearMult r v c =
  evalD v (d0 $ amult r c)
    == evalD v (mmult (liftToC . liftToTerm $ r) $ d0 c)

type D0LeibnizRule n = Vec N.Nat1 (V n) -> C n -> C n -> Bool
d0LeibnizRule :: N.SNatI n => D0LeibnizRule n
d0LeibnizRule v c1 c2 =
  evalD v (d0 $ sappend c1 c2)
    == evalD v (mmult c1 (d0 c2) <> mmult c2 (d0 c1))


type DLinearAdd p n = Vec (S p) (V n) -> TwoD p n
dLinearAdd :: N.SNatI n => DLinearAdd p n
dLinearAdd vs d1 d2 =
  evalD vs (d $ d1 <> d2) == evalD vs (d d1) <> evalD vs (d d2)

type DLinearMult p n = Number -> Vec (S p) (V n) -> OneD p n
dLinearMult :: N.SNatI n => DLinearMult p n
dLinearMult r vs d' =
  evalD vs (d $ mmult (liftToC . liftToTerm $ r) d')
    == evalD vs (mmult (liftToC . liftToTerm $ r) $ d d')

type DLeibnizRule p n = Vec (S (N.Plus p p)) (V n) -> TwoD p n
dLeibnizRule :: N.SNatI n => Number -> DLeibnizRule p n
dLeibnizRule r vs d1 d2 =
  let dProd = d $ exteriorProduct d1 d2
      dd1 = d d1
      dd2 = d d2
      prod1 = exteriorProduct dd1 d2
      prod2 = exteriorProduct dd2 d1 -- wrong way for types to match, sign needs to be flipped
      prod2Sign = mmult (liftToC . liftToTerm $ -r) prod2
  in evalD vs dProd == evalD vs (prod1 <> prod2Sign)

type DTwiceZero p n = Vec (S (S p)) (V n) -> OneD p n
dTwiceZero :: N.SNatI n => DTwiceZero p n
dTwiceZero vs d' = evalD vs (d . d $ d') == mempty


testD :: IO ()
testD = hspec $ do
  describe "Tests for D, D:" $ do
    prop "semigroup symmetric"
      (semigroupSymmetricD :: SemigroupSymmetricD N.Nat2 N.Nat3)
    prop "semigroup associative"
      (semigroupAssociatesD :: SemigroupAssociatesD N.Nat2 N.Nat3)
    prop "monoid left identity"
      (monoidLeftIdD :: MonoidLeftIdD N.Nat2 N.Nat3)
    prop "group has inverses"
      (groupInvD :: GroupInvD N.Nat2 N.Nat3)
    prop "module ring addition distributive"
      (moduleAddDistributes1D :: ModuleAddDistributes1D N.Nat2 N.Nat3)
    prop "module group addition distributive"
      (moduleAddDistributes2D :: ModuleAddDistributes2D N.Nat2 N.Nat3)
    prop "module multiplication associative"
      (moduleMultAssociatesD :: ModuleMultAssociatesD N.Nat2 N.Nat3)
    prop "module multiplication by 1 is identity"
      (module1IdD :: Module1IdD N.Nat2 N.Nat3)
    prop "addition linear"
      (linearAddD :: LinearAddD N.Nat2 N.Nat3)
    prop "multiplication by C n linear"
      (linearMultD :: LinearMultD N.Nat2 N.Nat3)

  describe "Tests for D, exterior product:" $ do
    prop "exterior product super commutative 1"
      (extProdSuperComm (Number 1) :: ExtProdSuperComm N.Nat2 N.Nat5)
    prop "exterior product super commutative 2"
      (extProdSuperComm (Number $ -1) :: ExtProdSuperComm N.Nat3 N.Nat7)

  describe "Tests for D, d0:" $ do
    prop "addition linear"
      (d0LinearAdd :: D0LinearAdd N.Nat3)
    prop "multiplication linear"
      (d0LinearMult :: D0LinearMult N.Nat3)
    prop "leibniz rule"
      (d0LeibnizRule :: D0LeibnizRule N.Nat3)

  describe "Tests for D, d:" $ do
    prop "addition linear"
      (dLinearAdd :: DLinearAdd N.Nat2 N.Nat3)
    prop "multiplication linear"
      (dLinearMult :: DLinearMult N.Nat2 N.Nat3)
    prop "leibniz rule1"
      (dLeibnizRule (Number 1) :: DLeibnizRule N.Nat3 N.Nat7)
    prop "leibniz rule2"
      (dLeibnizRule (Number $ -1) :: DLeibnizRule N.Nat2 N.Nat7)
    prop "dd = 0"
      (dTwiceZero :: DTwiceZero N.Nat1 N.Nat3)

