{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where

import Prelude hiding (putStrLn)
import Lib
import Diagrams.Prelude
import Diagrams.Backend.SVG.CmdLine
import Data.Comp.Multi
import Data.Comp.Multi.Dag

import Data.Text.Lazy.IO
import Data.GraphViz
import Data.GraphViz.Commands

m :: Diagram B
m = atop (square 2) $ circle 1 # fc blue # lw veryThick # lc purple # dashingG [0.2,0.5] 0 ||| circle 5

expression :: Term (Sig :+: Var) Int
expression = iLet (Tag 0) (2+3 :: Term (Sig :+: Var) Int) (iVar (Tag 0) * iLet (Tag 1) (iVar (Tag 0) + 5 :: Term (Sig :+: Var) Int) (iVar (Tag 1) * iVar (Tag 0) * iVar (Tag 1))) + 0*800+iVar (Tag 1)

graph :: Dag' (Sig :+: Var) Int
graph = removeLet $ termTree' expression

--main = runGraphvizCanvas Dot (toGraph graph) Xlib
main = runGraphvizCanvas Dot (toGraph $ termTree' expression) Xlib
--main = putStrLn . printDotGraph $ toGraph graph
--main = putStr . printDotGraph . toGraph $ termTree' expression
--main = mainWith $ toDiagram graph
