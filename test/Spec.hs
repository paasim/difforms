module Main where

import TestMat
import TestC
import TestV
import TestD
import TestPhi

main :: IO ()
main = do
  testMat
  testC
  testV
  testD
  testPhi

