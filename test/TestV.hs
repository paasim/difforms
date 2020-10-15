module TestV ( mainV ) where

import qualified Data.Type.Nat as N
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
type OneV n   = V n -> Terms n -> Bool
type TwoV n   = V n -> OneV n
type ThreeV n = V n -> TwoV n

-- V n, might be more interesting to define these as actions on C n
vsAssociates :: N.SNatI n => ThreeV n
vsAssociates v1 v2 v3 ts = evalV ((v1 `vsadd` v2) `vsadd` v3) ts
                        == evalV (v1 `vsadd` (v2 `vsadd` v3)) ts

vsCommutes :: N.SNatI n => TwoV n
vsCommutes v1 v2 ts = evalV (vsadd v1 v2) ts == evalV (vsadd v2 v1) ts

vsInv :: N.SNatI n => OneV n
vsInv v ts = evalV (vsadd v (vsinv v)) ts == evalV vsempty ts

vsmultAssociates :: N.SNatI n => Int -> Int -> OneV n
vsmultAssociates i1 i2 v ts = let d1 = fromIntegral i1
                                  d2 = fromIntegral i2
  in evalV (vsmult d1 (vsmult d2 v)) ts == (evalV (vsmult (d1*d2) v)) ts

vsmultLeftId :: N.SNatI n => OneV n
vsmultLeftId v ts = evalV (vsmult 1 v) ts == evalV v ts

vsmultDistributes :: N.SNatI n => Int -> Int -> TwoV n
vsmultDistributes i1 i2 v1 v2 ts = let d1 = fromIntegral i1
                                       d2 = fromIntegral i2
  in evalV (vsmult (d1 + d2) (vsadd v1 v2)) ts
      == evalV (vsadd (vsadd (vsmult d1 v1) (vsmult d1 v2))
                      (vsadd (vsmult d2 v1) (vsmult d2 v2))) ts

main :: IO ()
main = do
  qc "vector space associative" (vsAssociates :: ThreeV N.Nat3)
  qc "vector space commutative" (vsCommutes :: TwoV N.Nat3)
  qc "vector space invertible" (vsInv :: OneV N.Nat3)
  qc "vector space multiplication associative"
    (vsmultAssociates :: Int -> Int -> OneV N.Nat3)
  qc "vector space 1 multiplicative left identity" (vsmultLeftId :: OneV N.Nat3)
  qc "vector space multiplication distributive"
    (vsmultDistributes :: Int -> Int -> TwoV N.Nat3)


-- rename for exporting
mainV = main

