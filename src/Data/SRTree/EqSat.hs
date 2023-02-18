{-# language DeriveTraversable #-}
{-# language LambdaCase #-}
{-# language TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Data.SRTree.EqSat ( simplifyEqSat ) where

import Data.AEq

import Data.Eq.Deriving
import Data.Ord.Deriving
import Text.Show.Deriving

import Data.SRTree

import Control.Monad.State (State)
import qualified Control.Monad.State as ST

import Data.Maybe (isJust, isNothing)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set    as S
import qualified Data.Foldable as F

import Control.Applicative (liftA2)
import Control.Monad (unless)

{-
import Data.Equality.Utils
import Data.Equality.Matching
import Data.Equality.Saturation
import Data.Equality.Language
import Data.Equality.Analysis
import qualified Data.Equality.Graph.Lens as L
import Data.Equality.Graph.Monad as GM
import Data.Equality.Extraction


import Data.Equality.Graph.Lens hiding ((^.))
import Data.Equality.Matching.Database
import Data.Equality.Graph
-}

import Data.Equality.Graph.Lens hiding ((^.))
import qualified Data.Equality.Graph.Lens as L
import Data.Equality.Graph
import Data.Equality.Extraction
import Data.Equality.Analysis
import Data.Equality.Matching
import Data.Equality.Matching.Database
import Data.Equality.Saturation
import Data.Equality.Saturation.Scheduler

import Data.AEq

data SRTreeF a = VarF Int
               | ConstF Double
               | ParamF
               | FunF Function a
               | PowF a Int
               | AddF a a
               | SubF a a
               | MulF a a
               | DivF a a
               | PowerF a a
               | LogBaseF a a
               deriving (Functor, Foldable, Traversable)

deriveEq1 ''SRTreeF
deriveOrd1 ''SRTreeF
deriveShow1 ''SRTreeF

toFixTree :: SRTree Int Double -> Fix SRTreeF
toFixTree (Const x) = Fix (ConstF x)
toFixTree (Var x) = Fix (VarF x)
toFixTree (Param x) = Fix ParamF
toFixTree (Add l r) = Fix (AddF (toFixTree l) (toFixTree r))
toFixTree (Sub l r) = Fix (SubF (toFixTree l) (toFixTree r))
toFixTree (Mul l r) = Fix (MulF (toFixTree l) (toFixTree r))
toFixTree (Div l r) = Fix (DivF (toFixTree l) (toFixTree r))
toFixTree (Power l r) = Fix (PowerF (toFixTree l) (toFixTree r))
toFixTree (LogBase l r) = Fix (LogBaseF (toFixTree l) (toFixTree r))
toFixTree (Fun f n) = Fix (FunF f (toFixTree n))
toFixTree (Pow n i) = Fix (PowerF (toFixTree n) (Fix (ConstF $ fromIntegral i))) -- integral power can't be used for pattern rules
toFixTree Empty = undefined

toSRTree :: Fix SRTreeF -> SRTree Int Double
toSRTree (Fix (ConstF x)) = Const x
toSRTree (Fix (VarF x)) = Var x
toSRTree (Fix ParamF) = Param 0
toSRTree (Fix (AddF c1 c2)) = Add (toSRTree c1) (toSRTree c2)
toSRTree (Fix (SubF c1 c2)) = Sub (toSRTree c1) (toSRTree c2)
toSRTree (Fix (MulF c1 c2)) = Mul (toSRTree c1) (toSRTree c2)
toSRTree (Fix (DivF c1 c2)) = Div (toSRTree c1) (toSRTree c2)
toSRTree (Fix (PowerF c1 c2)) = Power (toSRTree c1) (toSRTree c2)
toSRTree (Fix (LogBaseF c1 c2)) = LogBase (toSRTree c1) (toSRTree c2)
toSRTree (Fix (FunF f c)) = Fun f (toSRTree c)
toSRTree (Fix (PowF f i)) = Pow (toSRTree f) i -- will never exists
{-
relabelParams :: SRTree Int Double -> SRTree Int Double
relabelParams t = (toState t) `ST.evalState` 0
  where
    toState :: SRTree Int Double -> State Int (SRTree Int Double)
    toState (Param x) = do n <- ST.get; ST.put (n+1); pure (Param n)
    toState (Add l r) = do l' <- toState l; r' <- toState r; pure (Add l' r')
    toState (Sub l r) = do l' <- toState l; r' <- toState r; pure (Sub l' r')
    toState (Mul l r) = do l' <- toState l; r' <- toState r; pure (Mul l' r')
    toState (Div l r) = do l' <- toState l; r' <- toState r; pure (Div l' r')
    toState (Power l (Const x)) = do l' <- toState l; if isInteger x then pure (Pow l' (round x)) else pure (Power l' (Const x))
    toState (Power l r) = do l' <- toState l; r' <- toState r; pure (Power l' r')
    toState (LogBase l r) = do l' <- toState l; r' <- toState r; pure (LogBase l' r')
    toState (Fun f n) = do n' <- toState n; pure (Fun f n')
    toState (Pow n i) = do n' <- toState n; pure (Pow n' i)
    toState n = pure n

    isInteger x = x == fromIntegral (round x)
-}
recountParams :: SRTree Int Double -> Int
recountParams t = (toState t) `ST.execState` 0
  where
    toState :: SRTree Int Double -> State Int (SRTree Int Double)
    toState (Param x) = do n <- ST.get; ST.put (n+1); pure (Param n)
    toState (Add l r) = do l' <- toState l; r' <- toState r; pure (Add l' r')
    toState (Sub l r) = do l' <- toState l; r' <- toState r; pure (Sub l' r')
    toState (Mul l r) = do l' <- toState l; r' <- toState r; pure (Mul l' r')
    toState (Div l r) = do l' <- toState l; r' <- toState r; pure (Div l' r')
    toState (Power l (Const x)) = do l' <- toState l; if isInteger x then pure (Pow l' (round x)) else pure (Power l' (Const x))
    toState (Power l r) = do l' <- toState l; r' <- toState r; pure (Power l' r')
    toState (LogBase l r) = do l' <- toState l; r' <- toState r; pure (LogBase l' r')
    toState (Fun f n) = do n' <- toState n; pure (Fun f n')
    toState (Pow n i) = do n' <- toState n; pure (Pow n' i)
    toState n = pure n

    isInteger x = x == fromIntegral (round x)
instance Num (Fix SRTreeF) where
  l + r = Fix $ AddF l r
  l - r = Fix $ SubF l r
  l * r = Fix $ MulF l r
  abs   = Fix . FunF Abs

  negate t    = fromInteger (-1) * t
  signum t    = undefined
  fromInteger = Fix . ConstF . fromInteger

instance OptIntPow (Fix SRTreeF) where
    t ^. x = Fix (PowF t x)

instance Fractional (Fix SRTreeF) where
    (/) a b = Fix (DivF a b)
    fromRational = Fix . ConstF . fromRational

instance Floating (Fix SRTreeF) where
  pi      = Fix (ConstF pi)
  exp     = Fix . FunF Exp
  log     = Fix . FunF Log
  sqrt    = Fix . FunF Sqrt
  sin     = Fix . FunF Sin
  cos     = Fix . FunF Cos
  tan     = Fix . FunF Tan
  asin    = Fix . FunF ASin
  acos    = Fix . FunF ACos
  atan    = Fix . FunF ATan
  sinh    = Fix . FunF Sinh
  cosh    = Fix . FunF Cosh
  tanh    = Fix . FunF Tanh
  asinh   = Fix . FunF ASinh
  acosh   = Fix . FunF ACosh
  atanh   = Fix . FunF ATanh

  l ** r      = Fix (PowerF l r)
  logBase l r = Fix (LogBaseF l r)

instance Num (Pattern SRTreeF) where
  l + r = NonVariablePattern $ AddF l r
  l - r = NonVariablePattern $ SubF l r
  l * r = NonVariablePattern $ MulF l r
  abs   = NonVariablePattern . FunF Abs

  negate t    = fromInteger (-1) * t
  signum t    = undefined
  fromInteger = NonVariablePattern . ConstF . fromInteger

instance OptIntPow (Pattern SRTreeF) where
    t ^. x = NonVariablePattern (PowF t x)

instance Fractional (Pattern SRTreeF) where
    (/) a b      = NonVariablePattern (DivF a b)
    fromRational = NonVariablePattern . ConstF . fromRational

instance Floating (Pattern SRTreeF) where
  pi      = NonVariablePattern (ConstF pi)
  exp     = NonVariablePattern . FunF Exp
  log     = NonVariablePattern . FunF Log
  sqrt    = NonVariablePattern . FunF Sqrt
  sin     = NonVariablePattern . FunF Sin
  cos     = NonVariablePattern . FunF Cos
  tan     = NonVariablePattern . FunF Tan
  asin    = NonVariablePattern . FunF ASin
  acos    = NonVariablePattern . FunF ACos
  atan    = NonVariablePattern . FunF ATan
  sinh    = NonVariablePattern . FunF Sinh
  cosh    = NonVariablePattern . FunF Cosh
  tanh    = NonVariablePattern . FunF Tanh
  asinh   = NonVariablePattern . FunF ASinh
  acosh   = NonVariablePattern . FunF ACosh
  atanh   = NonVariablePattern . FunF ATanh

  l ** r      = NonVariablePattern (PowerF l r)
  logBase l r = NonVariablePattern (LogBaseF l r)

instance Analysis (Maybe Double) SRTreeF where
    -- type Domain SRTreeF = Maybe Double
    makeA = evalConstant -- ((\c -> egr L.^._class c._data) <$> e)
    joinA ma mb = do
        a <- ma
        b <- mb
        !_ <- unless (abs (a-b) <= 1e-6 || a ~== b || (a == 0 && b == (-0)) || (a == (-0) && b == 0)) (error $ "Merged non-equal constants!" <> show a <> " " <> show b <> " " <> show (a==b))
        pure a
    modifyA cl = case cl L.^._data of
                 Nothing -> (cl, [])
                 Just d -> ((_nodes %~ S.filter (F.null .unNode)) cl, [Fix (ConstF d)])

evalConstant :: SRTreeF (Maybe Double) -> Maybe Double
evalConstant = \case
    -- Exception: Negative exponent: BinOp Pow e1 e2 -> liftA2 (^) e1 (round <$> e2 :: Maybe Integer)
    DivF e1 e2 -> liftA2 (/) e1 e2
    SubF e1 e2 -> liftA2 (-) e1 e2
    MulF e1 e2 -> liftA2 (*) e1 e2
    AddF e1 e2 -> liftA2 (+) e1 e2
    PowF e i -> (^^ i) <$> e
    PowerF e1 e2 -> liftA2 (**) e1 e2
    LogBaseF e1 e2 -> liftA2 logBase e1 e2
    FunF f e1 -> evalFun f <$> e1
    VarF _ -> Nothing
    ConstF x -> Just x -- TODO: investigate why it cannot handle NaN
    ParamF -> Nothing

instance Language SRTreeF

cost, cost2 :: CostFunction SRTreeF Int
cost2 = \case
  ConstF x -> 5
  VarF x -> 1
  AddF c1 c2 -> c1 + c2 + 1
  SubF c1 c2 -> c1 + c2 + 1 
  MulF c1 c2 -> c1 + c2 + 1
  DivF c1 c2 -> c1 + c2 + 1
  PowerF c1 c2 -> c1 + c2 + 1
  LogBaseF c1 c2 -> c1 + c2 + 1
  FunF _ c -> c + 1
  PowF _ _ -> undefined
  ParamF -> undefined

cost = \case
  ConstF x -> 5
  VarF x -> 2
  ParamF -> 10
  AddF c1 c2 -> 2 * c1 + c2
  SubF c1 c2 -> 2 * c1 + c2
  MulF c1 c2 -> 3 * c1 + c2
  DivF c1 c2 -> 3 * c1 + c2
  PowerF c1 c2 -> c1 + c2 + 5
  LogBaseF c1 c2 -> c1 + c2 + 5
  FunF Log c -> c + 3
  FunF _ c -> c * 5
  PowF _ _ -> undefined

unsafeGetSubst :: Pattern SRTreeF -> Subst -> ClassId
unsafeGetSubst (NonVariablePattern _) _ = error "unsafeGetSubst: NonVariablePattern; expecting VariablePattern"
unsafeGetSubst (VariablePattern v) subst = case IM.lookup v subst of
      Nothing -> error "Searching for non existent bound var in conditional"
      Just class_id -> class_id


is_not_zero :: Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_not_zero v subst egr =
    egr L.^._class (unsafeGetSubst v subst)._data /= Just 0

is_not_neg_consts :: Pattern SRTreeF -> Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_not_neg_consts v1 v2 subst egr =
    (fmap (>=0) (egr L.^._class (unsafeGetSubst v1 subst)._data) == Just True) ||
    (fmap (>=0) (egr L.^._class (unsafeGetSubst v2 subst)._data) == Just True)

is_negative :: Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_negative v subst egr =
    fmap (<0) (egr L.^._class (unsafeGetSubst v subst)._data) == Just True

is_const :: Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_const v subst egr =
    isJust (egr L.^._class (unsafeGetSubst v subst)._data)

is_one_const :: Pattern SRTreeF -> Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_one_const v1 v2 subst egr =
    let
      mb1 = (egr L.^._class (unsafeGetSubst v1 subst)._data)
      mb2 = (egr L.^._class (unsafeGetSubst v2 subst)._data)
    in case (mb1, mb2) of
      (Just _, Just _) -> False
      (Nothing, Nothing) -> False
      _ -> True

is_not_const :: Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_not_const v subst egr =
    isNothing (egr L.^._class (unsafeGetSubst v subst)._data)

rewritesBasic = 
    [   -- commutativity
        "x" + "y" := "y" + "x"
      , "x" * "y" := "y" * "x"
      -- associativity
      , "x" + ("y" + "z") := ("x" + "y") + "z"
      , "x" * ("y" * "z") := ("x" * "y") * "z"
      , "x" * ("y" / "z") := ("x" * "y") / "z"
      , ("x" * "y") / "z" := "x" * ("y" / "z")
      , ("a" * "x") * ("b" * "y") := ("a" * "b") * ("x" * "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "a" * "x" + "b" := "a" * ("x" + ("b" / "a")) :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "a" * "x" - "b" := "a" * ("x" - ("b" / "a")) :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "b" - "a" * "x" := "a" * (("b" / "a") - "x") :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "a" * "x" + "b" * "y" := "a" * ("x" + ("b" / "a") * "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "a" * "x" - "b" * "y" := "a" * ("x" - ("b" / "a") * "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "a" * "x" + "b" / "y" := "a" * ("x" + ("b" / "a") / "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "a" * "x" - "b" / "y" := "a" * ("x" - ("b" / "a") / "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"

      , "a" / ("b" * "x") := ("a" / "b") / "x" :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "x" / ("b" * "y") := (1 / "b") * "x" / "y" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" + "b" := ("x" + ("b" * "a")) / "a" :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "x" / "a" - "b" := ("x" - ("b" * "a")) / "a" :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "b" - "x" / "a" := (("b" * "a") - "x") / "a" :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "x" / "a" + "b" * "y" := ("x" + ("b" * "a") * "y") / "a" :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" + "y" / "b" := ("x" + "y" / ("b" * "a")) / "a" :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" - "b" * "y" := ("x" - ("b" * "a") * "y") / "a" :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" - "b" / "y" := ("x" - "y" / ("b" * "a")) / "a" :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , ("b" + "a" * "x") / ("c" + "d" * "y") := ("a"/"d") * ("b" / "a" + "x") / ("c" / "d" + "y") :| is_const "a" :| is_const "b" :| is_const "c" :| is_const "d"
      , ("b" + "x") / ("c" + "d" * "y") := (1/"d") * ("b" + "x") / ("c" / "d" + "y") :| is_const "b" :| is_const "c" :| is_const "d"
      -- identities
      , 0 + "x" := "x"
      , "x" - 0 := "x"
      , 1 * "x" := "x"
      , 0 * "x" := 0
      , 0 / "x" := 0
      -- cancellations 
      , "x" - "x" := 0
      , "x" / "x" := 1 :| is_not_zero "x"
      -- distributive and factorization
      , ("x" * "y") + ("x" * "z") := "x" * ("y" + "z") 
      , "x" - ("y" + "z") := ("x" - "y") - "z"
      , "x" - ("y" - "z") := ("x" - "y") + "z"
      , negate ("x" + "y") := negate "x" - "y" 
      , ("x" - "a") := "x" + negate "a" :| is_const "a" :| is_not_const "x"
      , ("x" - ("a" * "y")) := "x" + (negate "a" * "y") :| is_const "a" :| is_not_const "y"
      , (1 / "x") * (1 / "y") := 1 / ("x" * "y")
      -- multiplication of inverse
      , "x" * (1 / "x") := 1 :| is_not_zero "x"
      -- negate 
      , "x" - ( (-1) * "y") := "x" + "y" :| is_not_const "y"
      , "x" + negate "y" := "x" - "y" :| is_not_const "y"
      , 0 - "x" := negate "x" :| is_not_const "x"
   ]
rewritesFun = [
--        log ("x" * "y") := log "x" + log "y" :| is_not_neg_consts "x" "y" :| is_not_zero "x" :| is_not_zero "y" :| is_one_const "x" "y"
        log ("x" / "y") := log "x" - log "y" :| is_not_neg_consts "x" "y" :| is_not_zero "x" :| is_not_zero "y"
      , log ("x" ** "y") := "y" * log "x" :| is_not_neg_consts "x" "x" :| is_not_zero "x" 
      , log 1 := 0
      , log (sqrt "x") := 0.5 * log "x" :| is_not_const "x"
      , log (exp "x") := "x" :| is_not_const "x"
      , exp (log "x") := "x" :| is_not_const "x"
      , "x" ** (1/2) := sqrt "x"
      , sqrt ("a" * "x") := sqrt "a" * sqrt "x" :| is_not_neg_consts "a" "x"
      , sqrt ("a" * ("x" - "y")) := sqrt (negate "a") * sqrt ("y" - "x") :| is_negative "a"
      , sqrt ("a" * ("b" + "y")) := sqrt (negate "a") * sqrt ("b" - "y") :| is_negative "a" :| is_negative "b"
      , sqrt ("a" / "x") := sqrt "a" / sqrt "x" :| is_not_neg_consts "a" "x"
      , abs ("x" * "y") := abs "x" * abs "y"
    ]


rewriteTree t = fst $ equalitySaturation' (BackoffScheduler 2500 30) t (rewritesBasic <> rewritesFun) cost2

rewriteUntilNoChange rs 0 t = t
rewriteUntilNoChange rs n t
  | t == t'   = t'
  | otherwise = rewriteUntilNoChange (tail rs <> [head rs]) (n-1) t'
  where t' = (head rs) t

simplifyEqSat :: SRTree Int Double -> SRTree Int Double
simplifyEqSat = relabelParams . toSRTree . rewriteUntilNoChange [rewriteTree] 2 . toFixTree
