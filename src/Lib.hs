{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.Comp.Multi.Dag
import qualified Data.Comp as C
import qualified Data.Comp.Ops as C
import qualified Data.Comp.Show as C
import Data.Kind

type Tag = Int
newtype Val (a :: Type -> Type) (b :: Type) = Val {getVal :: Int}
data Pair a b where Pair :: a i -> a j -> Pair a (i,j)
data Add a b where Add :: a i -> a i -> Add a i
data Mult a b where Mult :: a i -> a i -> Mult a i
data Var a b where
    Var :: Tag -> Var a b
    Let :: Tag -> a sub -> a exp -> Var a exp

instance Show a => Show (K a b) where show = show . unK
instance Show a => Show (E (K a)) where show (E x) = show x

data LowerOrder (f :: (Type -> Type) -> Type -> Type) (a :: Type) = forall i . LowerOrder (f (K a) i)

instance HFunctor f => Functor (LowerOrder f) where
    fmap m (LowerOrder f) = LowerOrder $ hfmap (K . m . unK) f

instance HFoldable f => Foldable (LowerOrder f) where
    foldr m z (LowerOrder f) = hfoldr (m . unK) z f

instance (ShowHF f) => C.ShowF (LowerOrder f) where
    showF (LowerOrder x) = unK $ showHF x

type family SummandDecomp (f :: (Type -> Type) -> Type -> Type) :: Type where
    SummandDecomp (f :+: g) = (SummandDecomp f, SummandDecomp g)
    SummandDecomp _ = ()

class RemoveIndex (f :: (Type -> Type) -> Type -> Type) s (g :: Type -> Type) | f s -> g where
    removeIndex' :: forall a b. Proxy s -> f a b -> g (E a)
    removeIndexCxt' :: forall a b h. Proxy s -> Cxt h f a b -> C.Cxt (C h) g (E a)

instance HFunctor f => RemoveIndex f () (LowerOrder f) where
    removeIndex' _ = lowerOrder
    removeIndexCxt' _ (Hole x) = C.Hole $ E x
    removeIndexCxt' _ (Term x) = C.Term . LowerOrder $ hfmap (K . removeIndexCxt' (P @())) x

instance forall s f g s' f' g' . (RemoveIndex f s g, RemoveIndex f' s' g', HFunctor f, HFunctor f', Functor g, Functor g') => RemoveIndex (f :+: f') (s, s') (g C.:+: g') where
    removeIndex' _ (Inl x) = C.Inl $ removeIndex' (P @s) x
    removeIndex' _ (Inr x) = C.Inr $ removeIndex' (P @s') x
    removeIndexCxt' _ (Hole x) = C.Hole $ E x
    removeIndexCxt' _ (Term (Inl x)) = C.Term . C.Inl $ (\(E i) -> removeIndexCxt' (P @(s,s')) i) <$> removeIndex' (P @s) x
    removeIndexCxt' _ (Term (Inr x)) = C.Term . C.Inr $ (\(E i) -> removeIndexCxt' (P @(s,s')) i) <$> removeIndex' (P @s') x

removeIndex :: forall f g a b . RemoveIndex f (SummandDecomp f) g => f a b -> g (E a)
removeIndex = removeIndex' $ P @(SummandDecomp f)

removeIndexCxt :: forall f g a b h . RemoveIndex f (SummandDecomp f) g => Cxt h f a b -> C.Cxt (C h) g (E a)
removeIndexCxt = removeIndexCxt' $ P @(SummandDecomp f)

type family C x where
    C Hole = C.Hole
    C NoHole = C.NoHole

lowerOrder :: HFunctor f => f a b -> LowerOrder f (E a)
lowerOrder = LowerOrder . hfmap (K . E)

lowerOrderCxt :: HFunctor f => Cxt h f a :=> C.Cxt (C h) (LowerOrder f) (E a)
lowerOrderCxt (Hole x) = C.Hole $ E x
lowerOrderCxt (Term x) = C.Term . LowerOrder $ hfmap (K . lowerOrderCxt) x

$(derive [makeHFunctor, makeShowHF, makeHTraversable, makeHFoldable, smartAConstructors, smartConstructors]
            [''Val, ''Pair, ''Add, ''Mult, ''Var])

