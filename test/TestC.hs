module TestC ( testC ) where

import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.List.NonEmpty ( NonEmpty(..) )
import Test.QuickCheck
import Test.Hspec
import Test.Hspec.QuickCheck
import Common
import R
import C

-- Nothing to test with variables

-- Term
type OneTerm n   = Term n -> Bool
type TwoTerm n   = Term n -> OneTerm n
type ThreeTerm n = Term n -> TwoTerm n

type EvalLiftedTerm n = Number -> R n -> Bool
evalLiftedTerm :: EvalLiftedTerm n
evalLiftedTerm d r = evalTerm r (liftToTerm d) == d

semigroupSymmetricTerm :: TwoTerm n
semigroupSymmetricTerm r1 r2 = (r1 <> r2) == (r2 <> r1)

semigroupAssociatesTerm :: ThreeTerm n
semigroupAssociatesTerm r1 r2 r3 = ((r1 <> r2) <> r3) == (r1 <> (r2 <> r3))

monoidLeftIdTerm :: OneTerm n
monoidLeftIdTerm r = (mempty <> r) == r

-- C
type OneC n   = C n -> Bool
type TwoC n   = C n -> OneC n
type ThreeC n = C n -> TwoC n
type FourC n  = C n -> ThreeC n

type EvalLiftedC n = R n -> Term n -> Bool
evalLiftedC :: EvalLiftedC n
evalLiftedC r t = evalC r (liftToC t) == evalTerm r t

mkCIsIdempotent :: [Term n] -> Bool
mkCIsIdempotent ts = mkC ts == (mkC . cTerms . mkC) ts

semigroupSymmetric :: TwoC n
semigroupSymmetric r1 r2 = (r1 <> r2) == (r2 <> r1)

semigroupAssociates :: ThreeC n
semigroupAssociates r1 r2 r3 = ((r1 <> r2) <> r3) == (r1 <> (r2 <> r3))

monoidLeftId :: OneC n
monoidLeftId r = (mempty <> r) == r

semirngAssociates :: ThreeC n
semirngAssociates r1 r2 r3 = ((r1 `sappend` r2) `sappend` r3)
  == (r1 `sappend` (r2 `sappend` r3))

semirngLeftId :: OneC n
semirngLeftId r = (sempty `sappend` r) == r

semirngRightId :: OneC n
semirngRightId r = (r `sappend` sempty) == r

semiringDistributes :: FourC n
semiringDistributes r1 r2 r3 r4 = ((r1 <> r2) `sappend` (r3 <> r4))
  == ((r1 `sappend` r3) <> (r1 `sappend` r4) <> (r2 `sappend` r3) <> (r2 `sappend` r4))

semiringLeftAnnih :: OneC n
semiringLeftAnnih r = mempty `sappend` r == mempty

semiringRightAnnih :: OneC n
semiringRightAnnih r = r `sappend` mempty == mempty

amultAssociates :: Int -> Int -> OneC n
amultAssociates i1 i2 c = let d1 = fromIntegral i1
                              d2 = fromIntegral i2
  in amult (d1*d2) c == amult d1 (amult d2 c)

amultDistributes1 :: Int -> TwoC n
amultDistributes1 i c1 c2 = let d = fromIntegral i
  in amult d (c1 <> c2) == amult d c1 <> amult d c2

amultDistributes2 :: Int -> Int -> OneC n
amultDistributes2 i1 i2 c = let d1 = fromIntegral i1
                                d2 = fromIntegral i2
  in amult (d1 + d2) c == amult d1 c <> amult d2 c

testC :: IO ()
testC = hspec $ do
  describe "Tests for C, Term:" $ do
    prop "evaluating lifted double is identity"
      (evalLiftedTerm :: EvalLiftedTerm N.Nat3)
    prop "semigroup symmetric"
      (semigroupSymmetricTerm :: TwoTerm N.Nat3)
    prop "semigroup associative"
      (semigroupAssociatesTerm :: ThreeTerm N.Nat3)
  -- no need to test for right identity because the monoid is symmetric
    prop "monoid left identity"
      (monoidLeftIdTerm :: OneTerm N.Nat3)

  describe "Tests for C, C:" $ do
    prop "evaluating lifted term is the same as evaluating the term"
      (evalLiftedC :: EvalLiftedC N.Nat3)
    prop "semigroup symmetric"
      (semigroupSymmetric :: TwoC N.Nat3)
    prop "semigroup associative"
      (semigroupAssociates :: ThreeC N.Nat3)
  -- no need to test for right identity because the monoid is symmetric
    prop "monoid left identity"
      (monoidLeftId :: OneC N.Nat3)
    prop "semirng associative"
      (semirngAssociates :: ThreeC N.Nat3)
    prop "semirng left id"
      (semirngLeftId :: OneC N.Nat3)
    prop "semirng right id"
      (semirngRightId :: OneC N.Nat3)
    prop "semiring distributive"
      (semiringDistributes :: FourC N.Nat3)
    prop "semiring 0 left annihilator"
      (semiringLeftAnnih :: OneC N.Nat3)
    prop "semiring 0 right annihilator"
      (semiringRightAnnih :: OneC N.Nat3)
    prop "algebra multiplication associative"
      (amultAssociates :: Int -> Int -> OneC N.Nat3)
    prop "algebra multiplication distributive in double"
      (amultDistributes1 :: Int -> TwoC N.Nat3)
    prop "algebra multiplication distributive in terms"
      (amultDistributes2 :: Int -> Int -> OneC N.Nat3)

