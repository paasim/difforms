{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Phi where

import qualified Data.Map.Strict as M
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import Data.Type.Nat ( Nat(..) )
import qualified Data.Type.Nat as N
import Data.Fin ( Fin(..) )
import R

-- Linear maps (instead of any diffeomorphism)
type Phi' n m = Mat n m --Phi' { matPhi :: Vec m (Vec n Double) }

phiId' :: N.SNatI n => Phi' n n
phiId' = diagMat

-- rotation by theta
phi0' :: Double -> Phi' N.Nat2 N.Nat2
phi0' theta = Mat $ R (cos theta ::: (-1) * sin theta ::: VNil)
                ::: R (sin theta ::: cos theta ::: VNil)
                ::: VNil

-- This is what I would like to get
--newtype Phi n m = Phi { runPhi :: R n -> R m }

--instance Show (Phi n m) where
--  show _ = "Phi"

--phiId :: Phi n n 
--phiId = Phi id

-- rotation by theta
--phi0 :: Double -> Phi N.Nat2 N.Nat2
--phi0 theta = Phi $ R . f . x where
--  f (x ::: y ::: VNil) = x * cos theta + y * sin theta
--                    ::: -x * sin theta + y * cos theta
--                    ::: VNil


-- this assumes that Phi is linear
--phiToPhi' :: (N.SNatI n, N.SNatI m) => Phi n m -> Phi' n m
--phiToPhi' (Phi phi) = Mat . fmap (phi . R) $ diagMatrix where
--  diagMatrix :: N.SNatI n => Vec n (Vec n Double)
--  diagMatrix = V.map nthCoord V.universe
--  nthCoord :: N.SNatI n => Fin n -> Vec n Double
--  nthCoord n = V.imap (\ind -> \_ -> if ind == n then 1 else 0) $ V.repeat 0

--phi'ToPhi :: (N.SNatI n, N.SNatI m) => Phi' n m -> Phi n m
--phi'ToPhi phi' = Phi (\rn -> vecMatProduct rn phi')

