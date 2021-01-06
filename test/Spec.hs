module Main where

import TestR
import TestC
import TestV
import TestD
import TestPhi

main :: IO ()
main = do
  testR
  testC
  testV
  testD
  testPhi

