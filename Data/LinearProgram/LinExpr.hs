{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, DeriveFunctor #-}
module Data.LinearProgram.LinExpr (LinExpr(..), LinFunc, solve, substituteExpr, simplifyExpr,
        constTerm, coeffTerm, funcToExpr, linCombination) where

import Prelude hiding (lookup, filter, foldr)

import Control.Applicative
import Control.Monad
import qualified Data.Map as M
import Data.Map (Map)
import Linear.Vector

type LinFunc = Map
data LinExpr v c = LinExpr (LinFunc v c) c deriving (Eq, Read, Show, Functor)

constTerm :: LinExpr v c -> c
constTerm (LinExpr _ c) = c

coeffTerm :: LinExpr v c -> LinFunc v c
coeffTerm (LinExpr a _) = a

funcToExpr :: (Num c) => LinFunc v c -> LinExpr v c
funcToExpr = flip LinExpr 0

{-# INLINE linCombination #-}
-- | Given a set of basic variables and coefficients, returns the linear combination obtained
-- by summing.
linCombination :: (Ord v, Num r) => [(r, v)] -> LinFunc v r
linCombination xs = M.fromListWith (+) [(v, r) | (r, v) <- xs]

instance (Ord v) => Additive (LinExpr v) where
        zero = LinExpr zero 0
        LinExpr a1 c1 ^+^ LinExpr a2 c2 = LinExpr (a1 ^+^ a2) (c1 + c2)
        LinExpr a1 c1 ^-^ LinExpr a2 c2 = LinExpr (a1 ^-^ a2) (c1 - c2)

        liftU2 f (LinExpr a1 c1) (LinExpr a2 c2) = LinExpr (M.unionWith f a1 a2) (f c1 c2)
        liftI2 f (LinExpr a1 c1) (LinExpr a2 c2) = LinExpr (M.intersectionWith f a1 a2) (f c1 c2)

substituteExpr :: (Ord v, Num c) => v -> LinExpr v c -> LinExpr v c -> LinExpr v c
substituteExpr v expV expr@(LinExpr a c) = case M.lookup v a of
        Nothing -> expr
        Just k  -> LinExpr (M.delete v a) c ^+^ (k *^ expV)

simplifyExpr :: (Ord v, Num c) => LinExpr v c -> Map v (LinExpr v c) -> LinExpr v c
simplifyExpr (LinExpr a c) sol =
        M.foldrWithKey (const (^+^)) (LinExpr (M.difference a sol) c) (M.intersectionWith (*^) a sol)

solve :: (Ord v, Eq c, Fractional c) => [(LinFunc v c, c)] -> Maybe (Map v (LinExpr v c))
solve equs = solve' [LinExpr a (negate c) | (a, c) <- equs]

solve' :: (Ord v, Eq c, Fractional c) => [LinExpr v c] -> Maybe (Map v (LinExpr v c))
solve' (LinExpr a c:equs) = case M.minViewWithKey a of
        Nothing -> guard (c == 0) >> solve' equs
        Just ((x, a0), a') -> let expX = negated (recip a0 *^ LinExpr a' c) in
                liftM (simplifyExpr expX >>= M.insert x) (solve' (substituteExpr x expX <$> equs))
solve' [] = return M.empty

{-# RULES
        "mapWithKey/mapWithKey" forall f g m .
                M.mapWithKey f (M.mapWithKey g m) = M.mapWithKey (liftM2 (.) f g) m
        #-}
