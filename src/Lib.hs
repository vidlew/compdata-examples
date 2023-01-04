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
module Lib where

import Data.Comp.Multi
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.LowerOrder
import Data.Comp.Multi.Dag
import qualified Data.Comp as C
import qualified Data.Comp.Ops as C
import qualified Data.Comp.Show as C
import Data.Kind

type Tag = Int
data Val (a :: Type -> Type) (b :: Type) where Val :: Int -> Val a Int
data Pair a b where Pair :: a i -> a j -> Pair a (i,j)
data Add a b where Add :: a i -> a i -> Add a i
data Mult a b where Mult :: a i -> a i -> Mult a i
data Var a b where
    Var :: Tag -> Var a b
    Let :: Tag -> a sub -> a exp -> Var a exp


$(derive [makeHFunctor, makeShowHF, makeHTraversable, makeHFoldable, smartAConstructors, smartConstructors]
            [''Val, ''Pair, ''Add, ''Mult, ''Var])

