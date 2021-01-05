module Main where

import TestR
import TestC
import TestV
import TestD
import TestPhi

main :: IO ()
main = do
  mainR
  putStrLn ""
  mainC
  putStrLn ""
  mainV
  putStrLn ""
  mainD
  putStrLn ""
  mainPhi

