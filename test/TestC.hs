module TestC ( mainC ) where

import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Data.List.NonEmpty ( NonEmpty(..) )
import Test.QuickCheck
import Typeclasses
import R
import C
import TestHelpers

-- Nothing to test with variables

-- Term
type OneTerm n   = Term n -> Bool
type TwoTerm n   = Term n -> OneTerm n
type ThreeTerm n = Term n -> TwoTerm n

evalLiftedTerm :: Double -> R n -> Bool
evalLiftedTerm d r = evalTerm (liftToTerm d) r == d

mkTermIsIdempotent :: Double -> [Var n] -> Bool
mkTermIsIdempotent d vars = let t1 = mkTerm d vars
                            in t1 == mkTerm (termCoeff t1) (termVars t1)

semigroupSymmetricTerm :: TwoTerm n
semigroupSymmetricTerm r1 r2 = (r1 <> r2) == (r2 <> r1)

semigroupAssociatesTerm :: ThreeTerm n
semigroupAssociatesTerm r1 r2 r3 = ((r1 <> r2) <> r3) == (r1 <> (r2 <> r3))

monoidLeftIdTerm :: OneTerm n
monoidLeftIdTerm r = (mempty <> r) == r

-- Terms
type OneTerms n   = Terms n -> Bool
type TwoTerms n   = Terms n -> OneTerms n
type ThreeTerms n = Terms n -> TwoTerms n
type FourTerms n  = Terms n -> ThreeTerms n

evalLiftedTerms :: R n -> Term n -> Bool
evalLiftedTerms r t = evalTerms (liftToTerms t) r == evalTerm t r

mkTermsIsIdempotent :: Term n -> [Term n] -> Bool
mkTermsIsIdempotent t ts = let (Terms (t1 :| ts1)) = mkTerms t ts
                            in (Terms $ t1 :| ts1) == mkTerms t1 ts1

semigroupSymmetric :: TwoTerms n
semigroupSymmetric r1 r2 = (r1 <> r2) == (r2 <> r1)

semigroupAssociates :: ThreeTerms n
semigroupAssociates r1 r2 r3 = ((r1 <> r2) <> r3) == (r1 <> (r2 <> r3))

monoidLeftId :: OneTerms n
monoidLeftId r = (mempty <> r) == r

semirngAssociates :: ThreeTerms n
semirngAssociates r1 r2 r3 = ((r1 `sappend` r2) `sappend` r3)
  == (r1 `sappend` (r2 `sappend` r3))

semirngLeftId :: OneTerms n
semirngLeftId r = (sempty `sappend` r) == r

semirngRightId :: OneTerms n
semirngRightId r = (r `sappend` sempty) == r

semiringDistributes :: FourTerms n
semiringDistributes r1 r2 r3 r4 = ((r1 <> r2) `sappend` (r3 <> r4))
  == ((r1 `sappend` r3) <> (r1 `sappend` r4) <> (r2 `sappend` r3) <> (r2 `sappend` r4))

semiringLeftAnnih :: OneTerms n
semiringLeftAnnih r = mempty `sappend` r == mempty

semiringRightAnnih :: OneTerms n
semiringRightAnnih r = r `sappend` mempty == mempty

amultAssociates :: Int -> Int -> OneTerms n
amultAssociates i1 i2 ts = let d1 = fromIntegral i1
                               d2 = fromIntegral i2
  in amult (d1*d2) ts == amult d1 (amult d2 ts)

amultDistributes1 :: Int -> TwoTerms n
amultDistributes1 i ts1 ts2 = let d = fromIntegral i
  in amult d (ts1 <> ts2) == (amult d ts1) <> (amult d ts2)

amultDistributes2 :: Int -> Int -> OneTerms n
amultDistributes2 i1 i2 ts = let d1 = fromIntegral i1
                                 d2 = fromIntegral i2
  in amult (d1 + d2) ts == (amult d1 ts) <> (amult d2 ts)

main :: IO ()
main = do
  putStrLn "Tests for Term:"
  qc "evaluating lifted double is identity"
    (evalLiftedTerm :: Double -> R N.Nat3 -> Bool)
  qc "semigroup symmetric" (semigroupSymmetricTerm :: TwoTerm N.Nat3)
  qc "semigroup associative"  (semigroupAssociatesTerm :: ThreeTerm N.Nat3)
  -- no need to test for right identity because the monoid is symmetric
  qc "monoid left identity" (monoidLeftIdTerm :: OneTerm N.Nat3)

  putStrLn "Tests for Terms:"
  qc "evaluating lifted term is the same as evaluating the term"
    (evalLiftedTerms :: R N.Nat3 -> Term N.Nat3 -> Bool)
  qc "semigroup symmetric" (semigroupSymmetric :: TwoTerms N.Nat3)
  qc "semigroup associative"  (semigroupAssociates :: ThreeTerms N.Nat3)
  -- no need to test for right identity because the monoid is symmetric
  qc "monoid left identity" (monoidLeftId :: OneTerms N.Nat3)
  qc "semirng associative" (semirngAssociates :: ThreeTerms N.Nat3)
  qc "semirng left id" (semirngLeftId :: OneTerms N.Nat3)
  qc "semirng right id" (semirngRightId :: OneTerms N.Nat3)
  qc "semiring distributive" (semiringDistributes :: FourTerms N.Nat3)
  qc "semiring 0 left annihilator" (semiringLeftAnnih :: OneTerms N.Nat3)
  qc "semiring 0 right annihilator" (semiringRightAnnih :: OneTerms N.Nat3)
  qc "algebra multiplication associative"
    (amultAssociates :: Int -> Int -> OneTerms N.Nat3)
  qc "algebra multiplication distributive in double"
    (amultDistributes1 :: Int -> TwoTerms N.Nat3)
  qc "algebra multiplication distributive in terms"
    (amultDistributes2 :: Int -> Int -> OneTerms N.Nat3)


-- rename for exporting
mainC = main

