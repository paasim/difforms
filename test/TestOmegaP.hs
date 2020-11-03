{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module TestOmegaP ( mainOmegaP ) where

import qualified Data.Type.Nat as N
import Data.Type.Nat ( Nat(..) )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.List.NonEmpty ( NonEmpty(..) )
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import Omega
import OmegaP
import TestHelpers

-- Omega
type OneOP p n   = OmegaP p n -> Bool
type TwoOP p n   = OmegaP p n -> OneOP p n
type ThreeOP p n = OmegaP p n -> TwoOP p n

type SemigroupSymmetricOP p n = Vec p (V n) -> TwoOP p n
semigroupSymmetricOP :: N.SNatI n => SemigroupSymmetricOP p n
semigroupSymmetricOP vs o1 o2 =
  evalOmegaP vs (o1 <> o2) == evalOmegaP vs (o2 <> o1)

type SemigroupAssociatesOP p n = Vec p (V n) -> ThreeOP p n
semigroupAssociatesOP :: N.SNatI n => SemigroupAssociatesOP p n
semigroupAssociatesOP vs o1 o2 o3 =
  evalOmegaP vs ((o1 <> o2) <> o3) == evalOmegaP vs (o1 <> (o2 <> o3))

type MonoidLeftIdOP p n = Vec p (V n) -> OneOP p n
monoidLeftIdOP :: N.SNatI n => MonoidLeftIdOP p n
monoidLeftIdOP vs o = evalOmegaP vs (mempty <> o) == evalOmegaP vs o

type GroupInvOP p n = Vec p (V n) -> OneOP p n
groupInvOP :: N.SNatI n => GroupInvOP p n
groupInvOP vs o =
  evalOmegaP vs o <> evalOmegaP vs (ginv o) == evalOmegaP vs mempty
   && evalOmegaP vs (ginv o) <> evalOmegaP vs o == evalOmegaP vs mempty

type ModuleAddDistributes1OP p n = C n -> C n -> Vec p (V n) -> OneOP p n
moduleAddDistributes1OP :: N.SNatI n => ModuleAddDistributes1OP p n
moduleAddDistributes1OP c1 c2 vs o =
  evalOmegaP vs (mmult c1 o <> mmult c2 o) == evalOmegaP vs (mmult (c1 <> c2) o)

type ModuleAddDistributes2OP p n = C n -> Vec p (V n) -> TwoOP p n
moduleAddDistributes2OP :: N.SNatI n => ModuleAddDistributes2OP p n
moduleAddDistributes2OP c vs o1 o2 =
  evalOmegaP vs (mmult c o1 <> mmult c o2) == evalOmegaP vs (mmult c (o1 <> o2))

type ModuleMultAssociatesOP p n = C n -> C n -> Vec p (V n) -> OneOP p n
moduleMultAssociatesOP :: N.SNatI n => ModuleMultAssociatesOP p n
moduleMultAssociatesOP c1 c2 vs o =
  evalOmegaP vs (mmult c1 (mmult c2 o)) == evalOmegaP vs (mmult (c1 `sappend` c2) o)

type Module1IdOP p n = Vec p (V n) -> OneOP p n
module1IdOP :: N.SNatI n => Module1IdOP p n
module1IdOP vs o = evalOmegaP vs (mmult sempty o) == evalOmegaP vs o

type LinearAddOP p n = Vec p (V n) -> TwoOP p n
linearAddOP :: N.SNatI n => LinearAddOP p n
linearAddOP vs o1 o2 = evalOmegaP vs (o1 <> o2) == evalOmegaP vs o1 <> evalOmegaP vs o2

type LinearMultOP p n = C n -> Vec p (V n) -> OneOP p n
linearMultOP :: N.SNatI n => LinearMultOP p n
linearMultOP c vs o = evalOmegaP vs (mmult c o) == sappend c (evalOmegaP vs o)


type CotermPCotermId p n = CotermP p n -> Bool
cotermPCotermId :: N.SNatI p => CotermPCotermId p n
cotermPCotermId ctp =
  ctp == cotermToCotermP (cotermPToCoterm ctp)

type OmegaPOmegaId p n = Vec p (V n) -> OneOP p n
omegaPOmegaId :: N.SNatI p => OmegaPOmegaId p n
omegaPOmegaId vs op =
  evalOmegaP vs op == evalOmegaP vs (omegaToOmegaP . omegaPToOmega $ op)

type EvalOmegaEqual p1 p2 n = Vec p1 (V n) -> Vec p2 (V n) -> OneOP p1 n
evalOmegaEqual :: (N.Plus p1 p2 ~ n) => EvalOmegaEqual p1 p2 n
evalOmegaEqual v1 v2 op = evalOmegaP v1 op == evalOmega (v1 V.++ v2) (omegaPToOmega op)

type DEqual p1 p2 n = Vec (S p1) (V n) -> Vec p2 (V n) -> OneOP p1 n
dEqual :: (N.Plus (S p1) p2 ~ n, N.Plus p1 p2 ~ n1, N.SNatI n1) => DEqual p1 p2 n
dEqual v1 v2 op = evalOmegaP v1 (dP op) == evalOmega (v1 V.++ v2) (d . omegaPToOmega $ op)

type ExtProdEqual p1 p2 n = Vec n (V n) -> OmegaP p1 n -> OmegaP p2 n -> Bool
extProdEqual :: ExtProdEqual p1 p2 n
extProdEqual vs op1 op2 =
  evalOmega vs (exteriorProduct (omegaPToOmega op1) (omegaPToOmega op2))
    == evalOmega vs (omegaPToOmega $ exteriorProductP op1 op2)

type ExtProdSuperComm p1 p2 n = Vec n (V n) -> OmegaP p1 n -> OmegaP p2 n -> Bool
extProdSuperComm :: Rational -> ExtProdSuperComm p1 p2 n
extProdSuperComm r vs op1 op2 =
  let p = exteriorProductP op1 op2
      pFlip = exteriorProductP op2 op1
      pFlipSign = mmult (liftToC . liftToTerm $ r) pFlip
  in (evalOmega vs . omegaPToOmega $ p)
    == (evalOmega vs . omegaPToOmega $ pFlipSign)


type D0LinearAdd n = Vec N.Nat1 (V n) -> C n -> C n -> Bool
d0LinearAdd :: N.SNatI n => D0LinearAdd n
d0LinearAdd v c1 c2 =
  evalOmegaP v (d0 c1 <> d0 c2) == evalOmegaP v (d0 $ c1 <> c2)

type D0LinearMult n = Rational -> Vec N.Nat1 (V n) -> C n -> Bool
d0LinearMult :: N.SNatI n => D0LinearMult n
d0LinearMult r v c =
  evalOmegaP v (d0 $ amult r c)
    == evalOmegaP v (mmult (liftToC . liftToTerm $ r) $ d0 c)

type D0LeibnizRule n = Vec N.Nat1 (V n) -> C n -> C n -> Bool
d0LeibnizRule :: N.SNatI n => D0LeibnizRule n
d0LeibnizRule v c1 c2 =
  evalOmegaP v (d0 $ sappend c1 c2)
    == evalOmegaP v (mmult c1 (d0 c2) <> mmult c2 (d0 c1))


type DLinearAdd n = Vec n (V n) -> Omega n -> Omega n -> Bool
dLinearAdd :: N.SNatI n => DLinearAdd n
dLinearAdd vs o1 o2 =
  evalOmega vs (d $ o1 <> o2) == evalOmega vs (d o1) <> evalOmega vs (d o2)

type DLinearMult n = Rational -> Vec n (V n) -> Omega n -> Bool
dLinearMult :: N.SNatI n => DLinearMult n
dLinearMult r vs o =
  evalOmega vs (d $ mmult (liftToC . liftToTerm $ r) o)
    == evalOmega vs (mmult (liftToC . liftToTerm $ r) $ d o)

type DLeibnizRule p n = Vec n (V n) -> OmegaP p n  -> Omega n -> Bool
dLeibnizRule :: N.SNatI n => Rational -> DLeibnizRule p n
dLeibnizRule r vs op1 o2 =
  let dProd = d $ exteriorProduct (omegaPToOmega op1) o2
      dOp1 = dP op1
      dO2 = d o2
      prodD1 = exteriorProduct (omegaPToOmega dOp1) o2
      prodD2 = exteriorProduct (omegaPToOmega op1) dO2
      prodD2Sign = mmult (liftToC . liftToTerm $ r) prodD2
  in evalOmega vs dProd == evalOmega vs (prodD1 <> prodD2Sign)

type DTwiceZero n = Vec n (V n) -> Omega n -> Bool
dTwiceZero :: N.SNatI n => DTwiceZero n
dTwiceZero vs o = evalOmega vs (d . d $ o) == mempty


main :: IO ()
main = do
  putStrLn "OmegaP compatible with Omega:"
  qc "mapping CotermP to Coterm and back is id"
    (cotermPCotermId :: CotermPCotermId N.Nat2 N.Nat3)
  qc "mapping OmegaP to Omega and back is id"
    (omegaPOmegaId :: OmegaPOmegaId N.Nat2 N.Nat3)
  qc "evalOmega and evalOmegaP are equal in Omega and OmegaP"
    (evalOmegaEqual :: EvalOmegaEqual N.Nat2 N.Nat1 N.Nat3)
  qc "d and dP are equal in Omega and OmegaP"
    (dEqual :: DEqual N.Nat1 N.Nat2 N.Nat4)
  qc "exteriorProduct and exteriorProductP are equal in Omega and OmegaP"
    (extProdEqual :: ExtProdEqual N.Nat3 N.Nat2 N.Nat6)
  qc "exteriorProduct and exteriorProductP are equal in Omega and OmegaP"
    (extProdEqual :: ExtProdEqual N.Nat2 N.Nat1 N.Nat6)

  putStrLn "Tests for OmegaP:"
  qc "semigroup symmetric"
    (semigroupSymmetricOP :: SemigroupSymmetricOP N.Nat2 N.Nat3)
  qc "semigroup associative"
    (semigroupAssociatesOP :: SemigroupAssociatesOP N.Nat2 N.Nat3)
  qc "monoid left identity"
    (monoidLeftIdOP :: MonoidLeftIdOP N.Nat2 N.Nat3)
  qc "group has inverses"
    (groupInvOP :: GroupInvOP N.Nat2 N.Nat3)
  qc "module ring addition distributive"
    (moduleAddDistributes1OP :: ModuleAddDistributes1OP N.Nat2 N.Nat3)
  qc "module group addition distributive"
    (moduleAddDistributes2OP :: ModuleAddDistributes2OP N.Nat2 N.Nat3)
  qc "module multiplication associative"
    (moduleMultAssociatesOP :: ModuleMultAssociatesOP N.Nat2 N.Nat3)
  qc "module multiplication by 1 is identity"
    (module1IdOP :: Module1IdOP N.Nat2 N.Nat3)
  qc "addition linear"
    (linearAddOP :: LinearAddOP N.Nat2 N.Nat3)
  qc "multiplication by C n linear"
    (linearMultOP :: LinearMultOP N.Nat2 N.Nat3)

  putStrLn "Tests for exterior product:"
  qc "exterior product super commutative 1"
    (extProdSuperComm 1 :: ExtProdSuperComm N.Nat3 N.Nat2 N.Nat6)
  qc "exterior product super commutative 2"
    (extProdSuperComm (-1) :: ExtProdSuperComm N.Nat1 N.Nat3 N.Nat5)

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
  qc "leibniz rule1"
    (dLeibnizRule 1 :: DLeibnizRule N.Nat2 N.Nat5)
  qc "leibniz rule2"
    (dLeibnizRule (-1) :: DLeibnizRule N.Nat3 N.Nat5)
  qc "dd = 0"
    (dTwiceZero :: DTwiceZero N.Nat3)

-- rename for exporting
mainOmegaP = main

