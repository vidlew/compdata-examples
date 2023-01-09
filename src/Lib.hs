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

{-# LANGUAGE NoMonomorphismRestriction #-}
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
import qualified Data.Comp.Multi.Dag.AG as AG
import Data.Comp.Projection
import qualified Data.Dependent.Sum as S
import qualified Data.Dependent.Map as M
import qualified Data.Comp as C
import qualified Data.Comp.Ops as C
import qualified Data.Comp.Show as C
import qualified Data.Comp.Dag as C
import qualified Data.IntMap as I
import Data.Kind
import Unsafe.Coerce

--import Diagrams.Prelude
--import Diagrams.Backend.SVG.CmdLine
--import Diagrams.TwoD.Arrow

import Data.GraphViz
import Data.GraphViz.Types.Canonical

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

class HTraversable f => Graphable f where
    nodeAttrs :: f a b -> Attributes
    edgeAttrs :: f a b -> [Attributes]

instance Graphable Val where
    nodeAttrs (Val n) = [shape Octagon, toLabel n, bgColor Azure] 
    edgeAttrs _ = []
instance Graphable Pair where
    nodeAttrs _ = [toLabel "Pair"]
    edgeAttrs _ = [[toLabel "first"],[toLabel "second"]]
instance Graphable Add where
    nodeAttrs _ = [toLabel "+"]
    edgeAttrs _ = [[arrowTo box], [arrowTo box]]
instance Graphable Mult where
    nodeAttrs _ = [toLabel "*"]
    edgeAttrs _ = [[arrowTo vee], [arrowTo vee]]
instance Graphable Var where
    nodeAttrs (Let (Tag x) _ _) = [toLabel $ "Let x_" ++ show x]
    nodeAttrs (Var (Tag x)) = [toLabel $ "x_" ++ show x]
    edgeAttrs Let {} = [[toLabel "="],[toLabel "in"]]
    edgeAttrs (Var _) = []
instance (Graphable f, Graphable g) => Graphable (f :+: g) where
    nodeAttrs = caseH nodeAttrs nodeAttrs
    edgeAttrs = caseH edgeAttrs edgeAttrs

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

type Sig = Val :+: Pair :+: Add :+: Mult

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

instance (Val :<: f, Add :<: f, Mult :<: f) => Num (Term f Int) where
    fromInteger = iVal . fromInteger
    (+) = iAdd
    (*) = iMult


{-
toDiagram :: forall f . (Drawable f, HFoldable f) => Dag' f :=> Diagram B
toDiagram Dag' {root', edges', nodeCount'} = let r = text (opName root') # fontSizeL 0.2 # fc black <> circle 0.2 # fc (colourOf root') # named (Nothing :: Maybe Int)
                                                 rootArrows :: Diagram B -> Diagram B
                                                 rootArrows = hfoldl (\f (Node n) -> f . connectOutside (Nothing :: Maybe Int) (Just n)) id root'
                                                 draw :: S.DSum Node (f Node) -> Diagram B
                                                 draw (Node n S.:=> f) = text (opName f) # fontSizeL 0.2 # fc black <> circle 0.2 # fc (colourOf f) # named (Just n)
                                                 nodes = atPoints (trailVertices . regPoly nodeCount' $ fromIntegral nodeCount'/5) . fmap draw $ M.toList edges'
                                                 makeArrows :: S.DSum Node (f Node) -> Diagram B -> Diagram B
                                                 makeArrows (Node m S.:=> g) = hfoldl (\f (Node n) -> f . connectOutside (Just m) (Just n)) id g
                                                 arrows = foldl (.) id . map makeArrows $ M.toList edges'
                                             in (r ||| nodes) # rootArrows # arrows

toDot :: forall f . Graphable f=> Dag' f :=> String
toDot Dag' {root', edges'} = let rootArrows = hfoldl (\s (Node n) -> s ++ "root" ++ " -> node_" ++ show n ++ ";\n") "" root'
                                 nodes = (\(Node n S.:=> f) -> "node_" ++ show n ++ " [label=\"" ++ opName f ++ "\"];\n") =<< M.toList edges'
                                 makeArrows (Node m S.:=> g) = hfoldl (\f (Node n) -> f ++ "node_" ++ show m ++ " -> " ++ "node_" ++ show n ++ ";\n") "" g
                                 arrows = makeArrows =<< M.toList edges'
                             in "digraph G {root [label=" ++ opName root' ++ "];\n" ++ nodes ++ rootArrows ++ arrows ++ "}"
-}

instance PrintDot (Maybe Int) where
    unqtDot Nothing = unqtDot (0 :: Int)
    unqtDot (Just n) = unqtDot $ (2*abs n) + if n<0 then 2 else 1

toGraph :: forall f . Graphable f=> Dag' f :=> DotGraph (Maybe Int)
toGraph Dag' {root', edges'} = let rootNode = DotNode {nodeID = Nothing, nodeAttributes = nodeAttrs root'}
                                   rootArrows = zipWith (\attrs n -> DotEdge {fromNode = Nothing, toNode = Just n, edgeAttributes = attrs}) (edgeAttrs root') (hfoldr ((:) . getNode) [] root')
                                   nodes = (\(Node n S.:=> f) -> DotNode {nodeID = Just n, nodeAttributes = nodeAttrs f}) <$> M.toList edges'
                                   makeArrows (Node m S.:=> f) = zipWith (\attrs n -> DotEdge {fromNode = Just m, toNode = Just n, edgeAttributes = attrs}) (edgeAttrs f) (hfoldr ((:) . getNode) [] f)
                                   arrows = makeArrows =<< M.toList edges'
                                   statements = DotStmts {
                                                           attrStmts = []
                                                         , subGraphs = []
                                                         , nodeStmts = rootNode:nodes
                                                         , edgeStmts = rootArrows ++ arrows
                                                         }
                               in DotGraph {
                                             strictGraph = False
                                           , directedGraph = True
                                           , graphID = Nothing
                                           , graphStatements = statements
                                           }
