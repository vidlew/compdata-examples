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
import Control.Monad (when)
import Data.Maybe (isJust, fromMaybe)
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
import qualified Data.IntMap as I
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
hasLet Dag' {root', edges'} = isJust (proj @Var root') || (any isJust . fmap (\(_ S.:=> a) -> void $ proj @Var a) $ M.toList edges')

-- remove all let bindings, assuming all variables have unique tags and are only bound once in the expression and only used within their scope
-- extremely ugly but seems to work
removeLet :: forall f i . (HTraversable f, Var :<: f) => Dag' f i -> Dag' f i
removeLet Dag' {root', edges'} = if hasLet d then removeLet d else d where
                                    d = relabel $ Dag' {root' = hfmap replaceTag newRoot, edges' = M.fromList edgesFinal, nodeCount' = length edgesFinal}
                                    -- construct mapping from tags to nodes
                                    initMap :: M.DMap Tag Node
                                    initIndex :: Int
                                    initEdges :: M.DMap Node (f Node)
                                    newRoot :: f Node i
                                    (initMap, initIndex, initEdges, newRoot) = case proj @Var root' of Just (Var _)             -> error "Free variable at top level."
                                                                                                       Just (Let v@(Tag _) s e) -> (M.singleton v $ Node initIndex,
                                                                                                                                    (1+) . foldr max 0 . fmap (\(Node n S.:=> _) -> n) $ M.toList edges',
                                                                                                                                    M.insert (Node initIndex) (edges' M.! s) edges',
                                                                                                                                    edges' M.! e)
                                                                                                       Nothing                  -> (M.empty,
                                                                                                                                    foldr max 0 . fmap (\(Node n S.:=> _) -> n) $ M.toList edges',
                                                                                                                                    edges',
                                                                                                                                    root')
                                    updateMap (n@(Node _) S.:=> x) = case proj @Var x of Just (Let v@(Tag _) s e) -> modify $ \ (varmap, index, edgemap) -> (M.insert v (Node $ index+1) varmap, index+1, M.insert (Node $ index+1) (edges' M.! s) $ M.adjust (const $ edgemap M.! e) n edgemap)
                                                                                         _                        -> return ()
                                    (tagMap, _, newEdges) = execState (traverse updateMap (M.toList edges')) (initMap, initIndex, initEdges)
                                    replaceTag :: forall x . Node x -> Node x
                                    replaceTag n@(Node _) = case proj @Var $ newEdges M.! n of Just (Var x@(Tag _)) -> tagMap M.! x
                                                                                               _ -> n
                                    edgesFinal = (\(a S.:=> b) -> a S.:=> hfmap replaceTag b) <$> M.toList newEdges

-- | Relabel edges and remove unreachable nodes.
relabel :: HTraversable f => Dag' f i -> Dag' f i
relabel Dag' {root', edges'} = Dag' r' (M.fromList e') $ length e' where
    start = execState (addNodes root') (0, I.empty)
    e = M.toList edges'
    addNode (Node n) = do (m, labels) <- get
                          if n `I.member` labels then return () else
                                             put (m+1, I.insert n m labels)
                          return $ K ()
    addNodes = hmapM addNode
    (_, nodeMap) = fix' (execState (mapM (\(Node l S.:=> x) -> do {(_,ls) <- get; when (I.member l ls) . void $ addNodes x}) e)) start
    fix' f i = if i == f i then i else fix' f $ f i
    r' = hfmap (\(Node n) -> Node (nodeMap I.! n)) root'
    e' = do Node n S.:=> x <- e
            if n `I.member` nodeMap then return $ Node (nodeMap I.! n) S.:=> hfmap (\(Node j) -> Node $ nodeMap I.! j) x
                                  else []

type Sig = Val :+: Pair :+: Add :+: Mult :+: Var

-- |ProductOfSums x y z w represents (x+y)*(z+w).
data ProductOfSums a b where ProductOfSums :: a b -> a b -> a b -> a b -> ProductOfSums a b

hasPattern :: forall f . (Add :<: f, Mult :<: f) => Dag' f :=> Bool
hasPattern Dag' {root', edges'} = match root' || any (\(_ S.:=> x) -> match x) (M.toList edges') where
                                                  match :: f Node :=> Bool
                                                  match f = case proj @Mult f of Nothing -> False
                                                                                 Just (Mult x@(Node _) y@(Node _)) -> fromMaybe False $ do Add _ _ <- proj $ edges' M.! x
                                                                                                                                           Add _ _ <- proj $ edges' M.! y
                                                                                                                                           return True

matchPattern :: forall f . (HTraversable f, Add :<: f, Mult :<: f, ProductOfSums :<: f) => Dag' f :-> Dag' f
matchPattern Dag' {root', edges', nodeCount'} =  if hasPattern t then matchPattern t else t where
                                                  t = relabel $ Dag' {root' = match root', edges' = M.fromList . fmap (\(n S.:=> x) -> n S.:=> match x) $ M.toList edges', nodeCount' = nodeCount'}
                                                  match :: f Node :-> f Node
                                                  match f = case proj @Mult f of Nothing -> f
                                                                                 Just (Mult x@(Node _) y@(Node _)) -> fromMaybe f $ do Add a b <- proj $ edges' M.! x
                                                                                                                                       Add c d <- proj $ edges' M.! y
                                                                                                                                       return . inj $ ProductOfSums a b c d

$(derive [makeHFunctor, makeShowHF, makeHTraversable, makeHFoldable, smartAConstructors, smartConstructors]
            [''Val, ''Pair, ''Add, ''Mult, ''Var, ''ProductOfSums])

