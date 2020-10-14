module TestR ( mainR ) where

import Test.QuickCheck
import Algebra
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import R

type FourR n = R n -> R n -> R n -> R n -> Bool

semiringDistributes :: N.SNatI n => FourR n
semiringDistributes r1 r2 r3 r4 = ((r1 <> r2) `sappend` (r3 <> r4))
  == ((r1 `sappend` r3) <> (r1 `sappend` r4) <> (r2 `sappend` r3) <> (r2 `sappend` r4))

main :: IO ()
main = do
  quickCheck (semiringDistributes :: FourR N.Nat3)

mainR = main
