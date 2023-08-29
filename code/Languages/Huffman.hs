{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Languages.Huffman where

import Dot
import Data.List (sortOn)
import Data.Bifunctor (first)
import Types

mkHuffman :: [(DotM Node, Float)] -> DotM Node
mkHuffman [] = pure $ Node 0
mkHuffman [a] = fst a
mkHuffman [a, b] = makeLabeledTree "" $ zip ["0", "1"] $ fmap fst [a, b]
mkHuffman (sortOn snd -> ((a, pa) : (b, pb) : xs)) =
  mkHuffman $ (makeLabeledTree "" [("0", a), ("1", b)], pa + pb) : xs

huffman :: ToDot a => [(a, Float)] -> DotM Node
huffman = mkHuffman . fmap (first toDot)


