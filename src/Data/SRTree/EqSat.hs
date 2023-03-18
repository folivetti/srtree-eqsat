{-# language DeriveTraversable #-}
{-# language LambdaCase #-}
{-# language TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module Data.SRTree.EqSat ( simplifyEqSat ) where

import Control.Applicative (liftA2)
import Control.Monad (unless)
import Data.AEq ( AEq((~==)) )
import Data.Eq.Deriving ( deriveEq1 )
import Data.Equality.Analysis ( Analysis(..) )
import Data.Equality.Graph ( ClassId, Language, ENode(unNode) )
import Data.Equality.Graph.Lens hiding ((^.))
import Data.Equality.Graph.Lens qualified as L
import Data.Equality.Matching
import Data.Equality.Matching.Database ( Subst )
import Data.Equality.Saturation
import Data.Equality.Saturation.Scheduler ( BackoffScheduler(BackoffScheduler) )
import Data.Foldable qualified as F
import Data.IntMap.Strict qualified as IM
import Data.Maybe (isJust, isNothing)
import Data.Ord.Deriving ( deriveOrd1 )
import Data.SRTree
import Data.Set qualified as S
import Text.Show.Deriving ( deriveShow1 )

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
toFixTree (Const x)     = Fix (ConstF x)
toFixTree (Var x)       = Fix (VarF x)
toFixTree (Param _)     = Fix ParamF
toFixTree (Add l r)     = Fix (AddF (toFixTree l) (toFixTree r))
toFixTree (Sub l r)     = Fix (SubF (toFixTree l) (toFixTree r))
toFixTree (Mul l r)     = Fix (MulF (toFixTree l) (toFixTree r))
toFixTree (Div l r)     = Fix (DivF (toFixTree l) (toFixTree r))
toFixTree (Power l r)   = Fix (PowerF (toFixTree l) (toFixTree r))
toFixTree (LogBase l r) = Fix (LogBaseF (toFixTree l) (toFixTree r))
toFixTree (Fun f n)     = Fix (FunF f (toFixTree n))
toFixTree (Pow n i)     = Fix (PowerF (toFixTree n) (Fix (ConstF $ fromIntegral i))) -- integral power can't be used for pattern rules
toFixTree Empty         = undefined

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

instance Num (Fix SRTreeF) where
  l + r = Fix $ AddF l r
  l - r = Fix $ SubF l r
  l * r = Fix $ MulF l r
  abs   = Fix . FunF Abs

  negate t    = fromInteger (-1) * t
  signum _    = undefined
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
  signum _    = undefined
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

cost, costOut :: CostFunction SRTreeF Int
cost = \case
  ConstF _ -> 5
  VarF _ -> 1
  AddF c1 c2 -> c1 + c2 + 1
  SubF c1 c2 -> c1 + c2 + 1
  MulF c1 c2 -> c1 + c2 + 1
  DivF c1 c2 -> c1 + c2 + 1
  PowerF c1 c2 -> c1 + c2 + 1
  LogBaseF c1 c2 -> c1 + c2 + 1
  FunF _ c -> c + 1
  PowF _ _ -> undefined
  ParamF -> undefined

costOut = \case
  ConstF _ -> 5
  VarF _ -> 1
  AddF c1 c2 -> 2*c1 + 3*c2
  SubF c1 c2 -> 2*c1 + 3*c2
  MulF c1 c2 -> 2*c1 + 3*c2
  DivF c1 c2 -> 2*c1 + 3*c2
  PowerF c1 c2 -> 2*c1 + 3*c2
  LogBaseF c1 c2 -> 2*c1 + 3*c2
  FunF _ c -> 3*c
  PowF _ _ -> undefined
  ParamF -> undefined

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

is_not_const :: Pattern SRTreeF -> RewriteCondition (Maybe Double) SRTreeF
is_not_const v subst egr =
    isNothing (egr L.^._class (unsafeGetSubst v subst)._data)

rewritesBasic :: [Rewrite (Maybe Double) SRTreeF]
rewritesBasic =
    [   -- commutativity
        "x" + "y" := "y" + "x"
      , "x" * "y" := "y" * "x"
      -- associativity
      , ("x" + "y") + "z" := "x" + ("y" + "z")
      , ("x" * "y") * "z" := "x" * ("y" * "z")
      -- , "x" * ("y" / "z") := ("x" * "y") / "z"
      , ("x" * "y") / "z" := "x" * ("y" / "z")
      -- distributive and factorization
      , "x" - ("y" + "z") := ("x" - "y") - "z"
      , "x" - ("y" - "z") := ("x" - "y") + "z"
      , negate ("x" + "y") := negate "x" - "y"
      , ("x" - "a") := "x" + negate "a" :| is_const "a" :| is_not_const "x"
      , ("x" - ("a" * "y")) := "x" + (negate "a" * "y") :| is_const "a" :| is_not_const "y"
      , (1 / "x") * (1 / "y") := 1 / ("x" * "y")
   ]

-- Rules for nonlinear functions
rewritesFun :: [Rewrite (Maybe Double) SRTreeF]
rewritesFun = [
        log ("x" * "y") := log "x" + log "y" :| is_not_neg_consts "x" "x" :| is_not_zero "x" 
      , "x" ** "a" * "x" ** "b" := "x" ** ("a" + "b")
      , log ("x" / "y") := log "x" - log "y" :| is_not_neg_consts "x" "x" :| is_not_zero "x" 
      , log ("x" ** "y") := "y" * log "x" :| is_not_neg_consts "y" "y" :| is_not_zero "y"
      , log (sqrt "x") := 0.5 * log "x" :| is_not_const "x"
      , log (exp "x") := "x" :| is_not_const "x"
      , exp (log "x") := "x" :| is_not_const "x"
      , "x" ** (1/2) := sqrt "x"
      , sqrt ("a" * "x") := sqrt "a" * sqrt "x" :| is_not_neg_consts "a" "x"
      , sqrt ("a" * ("x" - "y")) := sqrt (negate "a") * sqrt ("y" - "x") :| is_negative "a"
      , sqrt ("a" * ("b" + "y")) := sqrt (negate "a") * sqrt ("b" - "y") :| is_negative "a" :| is_negative "b"
      , sqrt ("a" / "x") := sqrt "a" / sqrt "x" :| is_not_neg_consts "a" "x"
      , abs ("x" * "y") := abs "x" * abs "y" -- :| is_const "x"
    ]

-- Rules that reduces redundant parameters
constReduction :: [Rewrite (Maybe Double) SRTreeF]
constReduction = [
      -- identities
        0 + "x" := "x"
      , "x" - 0 := "x"
      , 1 * "x" := "x"
      , 0 * "x" := 0
      , 0 / "x" := 0
      -- cancellations 
      , "x" - "x" := 0
      , "x" / "x" := 1 :| is_not_zero "x"
      , "x" ** 1 := "x"
      -- multiplication of inverse
      , "x" * (1 / "x") := 1 :| is_not_zero "x"
      , ("x" * "y") + ("x" * "z") := "x" * ("y" + "z")
      -- negate 
      , "x" - ( (-1) * "y") := "x" + "y" :| is_not_const "y"
      , "x" + negate "y" := "x" - "y" :| is_not_const "y"
      , 0 - "x" := negate "x" :| is_not_const "x" 
      -- constant fusion
      , ("a" * "x") * ("b" * "y") := ("a" * "b") * ("x" * "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "a" / ("b" * "x") := ("a" / "b") / "x" :| is_const "a" :| is_const "b" :| is_not_const "x"
    ]

-- Rules that moves parameters to the outside and to the left
constFusion :: [Rewrite (Maybe Double) SRTreeF]
constFusion = [
        "a" * "x" + "b" := "a" * ("x" + ("b" / "a")) :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "a" * "x" + "b" / "y" := "a" * ("x" + ("b" / "a") / "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "a" * "x" - "b" / "y" := "a" * ("x" - ("b" / "a") / "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / ("b" * "y") := (1 / "b") * "x" / "y" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" + "b" := (1 / "a") * ("x" + ("b" * "a")) :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "x" / "a" - "b" := (1 / "a") * ("x" - ("b" * "a")) :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "b" - "x" / "a" := (1 / "a") * (("b" * "a") - "x") :| is_const "a" :| is_const "b" :| is_not_const "x"
      , "x" / "a" + "b" * "y" := (1 / "a") * ("x" + ("b" * "a") * "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" + "y" / "b" := (1 / "a") * ("x" + "y" / ("b" * "a")) :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" - "b" * "y" := (1 / "a") * ("x" - ("b" * "a") * "y") :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
      , "x" / "a" - "b" / "y" := (1 / "a") * ("x" - "y" / ("b" * "a")) :| is_const "a" :| is_const "b" :| is_not_const "x" :| is_not_const "y"
    ]

rewriteTree rules n coolOff c t = fst $ equalitySaturation' (BackoffScheduler n coolOff) t rules c

rewriteFull, rewriteReduction, rewriteOut, rewriteFun :: Fix SRTreeF -> Fix SRTreeF
rewriteFull = rewriteTree (constReduction <> constFusion <> rewritesFun <> rewritesBasic) 300 30 cost
rewriteFun = rewriteTree (constReduction <> constFusion <> rewritesFun) 300 10 cost
rewriteOut = rewriteTree (constReduction <> constFusion <> rewritesFun) 300 10 costOut
rewriteReduction = rewriteTree (constReduction <> rewritesBasic) 300 10 cost

rewriteUntilNoChange :: [Fix SRTreeF -> Fix SRTreeF] -> Int -> Fix SRTreeF -> Fix SRTreeF
rewriteUntilNoChange _ 0 t = t
rewriteUntilNoChange rs n t
  | t == t'   = t'
  | otherwise = rewriteUntilNoChange (tail rs <> [head rs]) (n-1) t'
  where t' = head rs t

simplifyEqSat :: SRTree Int Double -> SRTree Int Double
-- simplifyEqSat = relabelParams . toSRTree . rewriteUntilNoChange [rewriteReduction, rewriteOut, rewriteFun, rewriteFull] 4 . toFixTree
simplifyEqSat = relabelParams . toSRTree . rewriteUntilNoChange [rewriteReduction, rewriteOut, rewriteFull, rewriteReduction] 4 . toFixTree
