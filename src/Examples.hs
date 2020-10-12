{-# LANGUAGE GADTs #-}
module Examples where

import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import Test.QuickCheck
import Algebra
import R
import Phi
import C


d0 = F.fin0
d1 = F.fin1

x0 :: Var N.Nat2
x0 = Var d0 0

x1 :: Var N.Nat2
x1 = Var d1 0

zeroTerm :: Term N.Nat2
zeroTerm = Term 0 [x1, x1]

term1 :: Term N.Nat2
term1 = mkTerm 2 [x1, x0, x0, x0]

term2 :: Term N.Nat2
term2 = mkTerm (-3) [x1, x1]

terms1 :: Terms N.Nat2
terms1 = mkTerms term2 [zeroTerm, term1, term2]


