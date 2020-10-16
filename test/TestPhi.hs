module TestPhi ( mainPhi ) where

import qualified Data.Type.Nat as N
import Test.QuickCheck
import Typeclasses
import R
import C
import V
import Phi
import TestHelpers

type PullbackType n m = Phi' n m -> Terms m -> R n -> Bool

pullbackDef :: (N.SNatI n, N.SNatI m) => PullbackType n m
pullbackDef phi tsm rn = evalTerms (pullback phi tsm) rn ==
                         evalTerms tsm (vecMatProduct rn phi)

type PushforwardType n m = Phi' n m -> V n -> Terms m -> R m -> Bool
pushforwardDef :: (N.SNatI n, N.SNatI m) => PushforwardType n m
pushforwardDef phi vn tsm rm =
  evalTerms (evalV (pushforward phi vn) tsm) rm ==
    evalTerms (evalV vn $ pullback phi tsm) (matVecProduct phi rm)

main :: IO ()
main = do
  qc "pullback works as expected" (pullbackDef :: PullbackType N.Nat3 N.Nat2)
  qc "pushforward works as expected" (pushforwardDef :: PushforwardType N.Nat3 N.Nat2)

-- rename for exporting
mainPhi = main

