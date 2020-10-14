module Main where

import Test.QuickCheck
import Algebra
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import qualified Data.Fin as F
import TestR

main :: IO ()
main = do
  mainR
