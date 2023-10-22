{-# OPTIONS_GHC -Wno-orphans #-}

module Languages.Tree where

import Data.String
import Types
import Dot


instance IsString a => IsString (LRose a) where
  fromString = LPure . fromString

instance (b ~ [LRose a], IsString a) => IsString (b -> LRose a) where
  fromString a x = LRose (fromString a) x

instance Num a => Num (LRose a) where
  fromInteger = LPure . fromInteger

instance (b ~ [LRose a], Num a) => Num (b -> LRose a) where
  fromInteger a x = LRose (fromInteger a) x

asRose :: LRose String -> LRose String
asRose = id

asNRose :: LRose Int -> LRose Int
asNRose = id

asTrie :: Trie Metavar -> Trie Metavar
asTrie = id

