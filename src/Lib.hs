{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}
module Lib where

import Control.Monad.State
import Data.Maybe (isJust)
import Data.Typeable
import Data.GADT.Compare
import Data.Comp.Multi
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.LowerOrder
import Data.Comp.Multi.Dag
import qualified Data.Dependent.Sum as S
import qualified Data.Dependent.Map as M
import qualified Data.Comp as C
import qualified Data.Comp.Ops as C
import qualified Data.Comp.Show as C
import qualified Data.Comp.Dag as C
import Data.Kind
import Unsafe.Coerce

pairEq :: (a :~: b) -> (a' :~: b') -> (a,a') :~: (b,b')
pairEq Refl Refl = Refl

data Tag a where Tag :: Typeable a => Int -> Tag a
instance Show (Tag a) where show (Tag x) = show x

instance GEq Tag where
    a@(Tag x) `geq` b@(Tag y) = if typeOf a == typeOf b && x==y then Just $ unsafeCoerce Refl else Nothing

instance GCompare Tag where
    a@(Tag x) `gcompare` b@(Tag y) = case x `compare` y of
                                       LT -> GLT
                                       GT -> GGT
                                       EQ -> case typeOf a `compare` typeOf b of
                                              LT -> GLT
                                              GT -> GLT
                                              EQ -> unsafeCoerce GEQ

data Val (a :: Type -> Type) (b :: Type) where Val :: Int -> Val a Int
instance HFgeq Val where
    Val a `hfgeq` Val b = if a==b then Just Refl else Nothing

data Pair a b where Pair :: a i -> a j -> Pair a (i,j)
instance HFgeq Pair where
    Pair x y `hfgeq` Pair z w = do r <- x `geq` z
                                   l <- y `geq` w
                                   return $ pairEq r l

data Add a b where Add :: a i -> a i -> Add a i
instance HFgeq Add where
    Add x y `hfgeq` Add z w = do _ <- x `geq` z
                                 y `geq` w

data Mult a b where Mult :: a i -> a i -> Mult a i
instance HFgeq Mult where
    Mult x y `hfgeq` Mult z w = do _ <- x `geq` z
                                   y `geq` w

data Var a b where
    Var :: Tag b -> Var a b
    Let :: Tag sub -> a sub -> a exp -> Var a exp
instance HFgeq Var where
    Var u `hfgeq` Var v = u `geq` v
    Let u s e `hfgeq` Let v t f = do _ <- u `geq` v
                                     _ <- s `geq` t
                                     e `geq` f
    _ `hfgeq` _ = Nothing

hasLet :: (Var :<: f) => Dag' f i -> Bool
hasLet Dag' {root', edges'} = case proj @Var root' of
                                Just _ -> True
                                Nothing ->
                                    any isJust . fmap (\(_ S.:=> a) -> void $ proj @Var a) $ M.toList edges'

removeLet :: forall f i . Var :<: f => Dag' f i -> Dag' f i
removeLet Dag' {root', edges'} = let
                  e' = M.toList edges'
                  r = case proj @Var root' of
                        Just (Let _ _ expr) -> edges' M.! expr
                        Just (Var _       ) -> error "Free variable at top level, this should not happen"
                        Nothing             -> root'
                  initTab = case proj @Var root' of
                        Just (Let v sub _) -> M.singleton v $ edges' M.! sub
                        Just (Var _)       -> error "Free variable at top level, this should not happen"
                        Nothing            -> M.empty
                  run :: S.DSum Node (f Node) -> State (M.DMap Node (f Node), M.DMap Tag (f Node)) ()
                  run (Node i S.:=> a) =
                      case proj @Var a of
                        Just (Let v sub expr) -> do (m, tab) <- get
                                                    let m' = M.insert (Node i) (edges' M.! expr) m
                                                    let tab' = M.insert v (edges' M.! sub) tab
                                                    put (m', tab')
                        Just (Var v)          -> do (m, tab) <- get
                                                    let m' = M.insert (Node i) (tab M.! v) m
                                                    put (m', tab)
                        Nothing               -> do (m, tab) <- get
                                                    put (M.insert (Node i) a m, tab)
                  (eFinal, _) = execState (mapM_ run e') (M.empty, initTab)
                  d = Dag' r eFinal . length $ M.toList eFinal
                in if hasLet d then removeLet d else d

type Sig = Val :+: Pair :+: Add :+: Mult :+: Var

-- |ProductOfSums x y z w represents (x+y)*(z+w).
data ProductOfSums a b where ProductOfSums :: a b -> a b -> a b -> a b -> ProductOfSums a b

hasPattern :: (Add :<: f, Mult :<: f) => Dag' f :=> Bool
hasPattern Dag' {root', edges'} = undefined

matchPattern :: (Add :<: f, Mult :<: f, ProductOfSums :<: f) => Dag' f :-> Dag' f
matchPattern Dag' {root', edges', nodeCount'} = undefined

$(derive [makeHFunctor, makeShowHF, makeHTraversable, makeHFoldable, smartAConstructors, smartConstructors]
            [''Val, ''Pair, ''Add, ''Mult, ''Var, ''ProductOfSums])

