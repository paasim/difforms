module Main where

import TestR
import TestC
import TestV
import TestPhi
import TestOmega
import TestOmegaP

main :: IO ()
main = do
  mainR
  mainC
  mainV
  mainPhi
  mainOmega
  mainOmegaP

