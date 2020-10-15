module TestHelpers where

import Test.QuickCheck

qc :: Testable prop => String -> prop -> IO ()
qc str prop = quickCheck . label str $ prop

