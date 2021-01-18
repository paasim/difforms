{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module I where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), Plus )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Common
import C
import D

data E p n = E { eC :: C n, eDims :: Vec p (Fin n) } deriving (Eq, Ord)

instance Show (E p n) where
  show e = "E:\n " <> show (eC e)
                   <> "\n Evaluated at the boundaries of: "
                   <> (L.intercalate ", " . V.toList . fmap (("x_" <>) . show) . eDims $ e)

getBoundaries :: Vec n Number -> Vec n Number -> E p n -> Vec p (Number, Number)
getBoundaries from to = fmap (\dim -> (from V.! dim, to V.! dim)) . eDims

liftToE :: C n -> E Z n
liftToE c = E c VNil

emultC :: C n -> E p n -> E p n
emultC c e = E (sappend c $ eC e) $ eDims e

eAddDims :: Vec p1 (Fin n) -> E p2 n -> E (Plus p1 p2) n
eAddDims dims e = E (eC e) $ dims V.++ eDims e

evalE :: E p n -> Vec p (Number, Number) -> C n
evalE e = foldr (uncurry cDiff) (eC e) . V.zipWith (,) (eDims e)

cDiff :: Fin n -> (Number, Number) -> C n -> C n
cDiff dim (f, t) c = partialEvalC t dim c <> ginv (partialEvalC f dim c)

iCFin :: Vec p (Fin n) -> C n -> E p n
iCFin dims c = E (foldr antiD c dims) dims

iEFin :: Vec p (Fin n) -> E p1 n -> E (Plus p1 p) n
iEFin cvs e = eAddDims (eDims e) $ iCFin cvs (eC e)

iE :: E p1 n -> Coterm p n -> E (Plus p1 p) n
iE e ct = emultC (cotermC ct) . iEFin (fmap covarDim . cotermVars $ ct) $ e

i' :: C n -> D p n -> [E p n]
i' c = fmap (iE (liftToE c)) . dCoterms

i :: Vec n Number -> Vec n Number -> C n -> D p n -> Number
i froms tos c = evalC froms . foldMap (\e -> evalE e (getBoundaries froms tos e)) . i' c

