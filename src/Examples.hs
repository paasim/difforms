{-# LANGUAGE GADTs #-}
module Examples where

import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Test.QuickCheck
import Typeclasses
import R
import Phi
import C


d0 = F.fin0
d1 = F.fin1
d2 = F.fin2

x0 :: Var N.Nat3
x0 = Var d0 2

x1 :: Var N.Nat3
x1 = Var d1 2

x2 :: Var N.Nat3
x2 = Var d2 13

zeroTerm :: Term N.Nat3
zeroTerm = Term 0 [x1, x1]

term1 :: Term N.Nat3
term1 = mkTerm 2 [x1, x0, x0, x0]

term2 :: Term N.Nat3
term2 = mkTerm (-3) [x1, x1]

terms1 :: Terms N.Nat3
terms1 = mkTerms term2 [zeroTerm, term1, term2]

term21 = mkTerm (-3) [x0, x1, x2]

var20 = Var d0 9
var21 = Var d1 2
var22 = Var d2 5

term22 = mkTerm 1 [var20, var21, var22]

