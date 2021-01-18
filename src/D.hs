{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module D where

import Data.Fin ( Fin(..) )
import Data.Type.Nat ( Nat(..), Plus, SNatI )
import Data.Vec.Lazy ( Vec(..) )
import qualified Data.Vec.Lazy as V
import qualified Data.List as L
import Test.QuickCheck
import Common
import Mat
import C
import V


-- dx, dy etc
newtype Covar n = Covar { covarDim :: Fin n } deriving (Eq, Ord)

instance Show (Covar n) where
  show (Covar n)    = "dx_" <> show n

instance SNatI n => Arbitrary (Covar n) where
  arbitrary = Covar <$> (elements . V.toList $ V.universe)

evalCovar :: V n -> Covar n -> C n
evalCovar v cv = vComp v V.! covarDim cv


-- ZeroCoterm corresponds to the case where C n is mempty
data Coterm p n = ZeroCoterm | Coterm (Vec p (Covar n)) (C n) deriving (Eq, Ord)

instance Show (Coterm p n) where
  show ZeroCoterm = show (mempty :: C n)
  show (Coterm VNil c) =
    "(" <> show c <> ")"
  show (Coterm cvs c) =
    "(" <> show c <> ")*" <> (L.intercalate "*" . fmap show  . V.toList $ cvs)

-- "semigroupoid" multiplication
cotermMappend :: Coterm p1 n -> Coterm p2 n -> Coterm (Plus p1 p2) n
cotermMappend ZeroCoterm _ = ZeroCoterm
cotermMappend _ ZeroCoterm = ZeroCoterm
cotermMappend (Coterm cvs c) (Coterm cvs' c') = mkCoterm (cvs V.++ cvs') $ sappend c c'

-- multiplicative identity
cotermMempty :: Coterm Z n
cotermMempty = liftToCoterm sempty

-- module multiplication (though group missing)
ctpMult :: C n -> Coterm p n -> Coterm p n
ctpMult _  ZeroCoterm     = ZeroCoterm
ctpMult c' (Coterm cvs c) = mkCoterm cvs $ sappend c' c

instance (SNatI p, SNatI n) => Arbitrary (Coterm p n) where
  -- in order to prevent oveflow when evaluating terms
  arbitrary = mkCoterm <$> arbitrary <*> arbitrary

liftToCoterm :: C n -> Coterm Z n
liftToCoterm = Coterm VNil

mkCoterm :: Vec p (Covar n) -> C n -> Coterm p n
mkCoterm cvs c = let (isEven, cvs') = bubbleVec cvs
  in case (c == mempty || not (uniqSortedVec cvs'), isEven) of
    (True,  _) -> ZeroCoterm --coef is zero or two coterms of same dimension
    (_,  True) -> Coterm cvs' c
    (_, False) -> negateCoterm $ Coterm cvs' c -- negate because of anticommutativity

evalCoterm :: Vec (S p) (V n) -> Coterm (S p) n -> C n
evalCoterm _  ZeroCoterm     = mempty
evalCoterm vs (Coterm cvs c) =
  sappend c . det . Mat . fmap (\v -> fmap (evalCovar v) cvs) $ vs

negateCoterm :: Coterm p n -> Coterm p n
negateCoterm ZeroCoterm     = ZeroCoterm
negateCoterm (Coterm cvs c) = Coterm cvs $ ginv c

-- keeps track of the permutation (even or odd)
insertVec :: Ord a => a -> Bool -> Vec n a -> (Bool, Vec (S n) a)
insertVec a b VNil = (b, a ::: VNil)
insertVec a b (a' ::: rest) = if a < a'
  then (b, a ::: a' ::: rest)
  else (a' :::) <$> insertVec a (not b) rest

-- bubblesort, but keeps track of whether the
-- sorted list is an even permutation
bubbleVec :: Ord a => Vec n a -> (Bool, Vec n a)
bubbleVec VNil = (True, VNil)
bubbleVec (a ::: as) = uncurry (insertVec a) $ bubbleVec as

-- check whether all the elements are unique,
-- assumes that the vec is sorted
uniqSortedVec :: Eq a => Vec n a -> Bool
uniqSortedVec VNil                 = True
uniqSortedVec (_ ::: VNil)         = True
uniqSortedVec (a1 ::: a2 ::: rest) = a1 /= a2 && uniqSortedVec (a2 ::: rest)


-- for constructing valid instances of D
cotermVarsEq :: Coterm p n -> Coterm p n -> Bool
cotermVarsEq ct1 ct2 = getCvs ct1 == getCvs ct2 where
  getCvs ZeroCoterm     = Nothing
  getCvs (Coterm cvs _) = Just cvs

-- Sum of two terms assuming the vars are equal
cotermSum :: Coterm p n -> Coterm p n -> Coterm p n
cotermSum ct             ZeroCoterm    = ct
cotermSum ZeroCoterm     ct            = ct
cotermSum (Coterm cvs c) (Coterm _ c') =
  if c <> c' == mempty then ZeroCoterm else Coterm cvs $ c <> c'

-- extract the coefficient from a coterm
cotermC :: Coterm p n -> C n
cotermC ZeroCoterm   = mempty
cotermC (Coterm _ c) = c

-- A differential form represented as a sum of nonzero coterm(s),
-- ie. differential forms such as, f(x1,x2,x3)dx_1dx_2 + g(x1,x2,x3)dx_2dx_3
-- where f,g are of type C 3
newtype D p n = Coterms { dCoterms :: [Coterm p n] }

instance Show (D p n) where
  show = (<>) "D:\n  " . L.intercalate "\n + " . fmap show . dCoterms

instance Semigroup (D p n) where
  dpn <> dpn' = sortedCotermsIntoD $ merge (dCoterms dpn) (dCoterms dpn')

instance Monoid (D p n) where
  mempty = Coterms []

instance Group (D p n) where
  ginv = mkD . fmap negateCoterm . dCoterms

instance Module (D p n) (C n) where
  mmult c = mkD . fmap (ctpMult c) . dCoterms

instance (SNatI p, SNatI n) => Arbitrary (D p n) where
  arbitrary = mkD <$> resize 4 arbitrary

liftToD :: Coterm p n -> D p n
liftToD ctp = mkD [ctp]

unliftD :: D Z n -> C n
unliftD = foldMap cotermC . dCoterms

evalD :: Vec (S p) (V n) -> D (S p) n -> C n
evalD vs = foldMap (evalCoterm vs) . dCoterms

mkD :: [Coterm p n] -> D p n
mkD = sortedCotermsIntoD . L.sort

sortedCotermsIntoD :: [Coterm p n] -> D p n
sortedCotermsIntoD = Coterms
                   -- Remove 0s from the sum
                   . filter (ZeroCoterm /=)
                   -- adx_1dx_2 + bdx_1dx_2 = (a+b)dx_1dx_2 etc.
                   . combineSimilar cotermVarsEq cotermSum

-- cotermMappend is the product (2dx_3 * 3dx_1 = -6dx_1dx_3)
extProdCoterm :: D p2 n -> Coterm p1 n -> D (Plus p1 p2) n
extProdCoterm dpn ct = mkD . fmap (cotermMappend ct) . dCoterms $ dpn

-- fold over the coterms
exteriorProduct :: D p1 n -> D p2 n -> D (Plus p1 p2) n
exteriorProduct dpn1 dpn2 = foldMap (extProdCoterm dpn2) . dCoterms $ dpn1

-- partial derivative with respect to a given dimension
dCotermBy :: Coterm p n -> Covar n -> Coterm (S p) n
dCotermBy ZeroCoterm     _  = ZeroCoterm
dCotermBy (Coterm cvs c) cv = mkCoterm (cv ::: cvs) (partialD c . covarDim $ cv)

-- fold over all the dimensions
dCoterm :: SNatI n => Coterm p n -> D (S p) n
dCoterm ct = foldMap (liftToD . dCotermBy ct . Covar) V.universe

-- foldr over coterms
d :: SNatI n => D p n -> D (S p) n
d = foldMap dCoterm . dCoterms

-- same as d but for C n which are interpreted as 0-forms (D Z n)
d0 :: SNatI n => C n -> D (S Z) n
d0 = d . liftToD . liftToCoterm

-- integrate C w.r.t. cv, however the integration limits
-- have to be specified for each dimension as Covar n
-- does not specify whether it is dx_0, dx_1 etc...
iC :: Vec n Number -> Vec n Number -> Covar n -> C n -> C n
iC froms tos cv c =
  partialEvalCAt tos dim ad <> ginv (partialEvalCAt froms dim ad) where
    dim = covarDim cv
    ad = antiD dim c

iCoterm :: Vec n Number -> Vec n Number -> C n -> Coterm p n -> C n
iCoterm _     _   _  ZeroCoterm     = mempty
iCoterm froms tos c' (Coterm cvs c) = sappend c $ foldr (iC froms tos) c' cvs

i :: D p n -> C n -> Vec n Number -> Vec n Number -> C n
i d c froms tos = foldMap (iCoterm froms tos c) . dCoterms $ d

i' :: D p n -> C n -> Vec n Number -> Vec n Number -> Number
i' d c froms tos = evalC froms $ i d c froms tos

data E p n = ZeroE | E (C n) (Vec p (Fin n)) deriving (Eq, Ord)

liftToE :: C n -> E Z n
liftToE c = E c VNil

evalE :: E p n -> Vec p Number -> Vec p Number -> C n
evalE ZeroE           _       _        = mempty
evalE (E c VNil)      _       _        = c
evalE (E c (d:::ds)) (f:::fs) (t:::ts) =
  let c' = partialEvalC t d c <> ginv (partialEvalC f d c)
  in evalE (E c' ds) fs ts

emultC :: C n -> E p n -> E p n
emultC _  ZeroE      = ZeroE
emultC c' (E c lims) = E (sappend c c') lims

iCFin :: Vec p (Fin n) -> C n -> E p n
iCFin VNil     c = E c VNil
iCFin (d:::ds) c = let (E c' ds') = iCFin ds c in E (antiD d c') $ d:::ds'

iEFin :: Vec p (Fin n) -> E p1 n -> E (Plus p1 p) n
iEFin _   ZeroE      = ZeroE
iEFin cvs (E c lims) = let (E c' lims') = iCFin cvs c in E c' $ lims V.++ lims'

iE :: Coterm p n -> E p1 n -> E (Plus p1 p) n
iE ZeroCoterm     = const ZeroE
iE (Coterm cvs c) = emultC c . iEFin (fmap covarDim cvs)

