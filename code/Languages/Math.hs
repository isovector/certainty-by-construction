{-# OPTIONS_GHC -Wno-missing-methods #-}
module Languages.Math where

import Dot
import Data.String
import Types

data MathLang = Times MathLang MathLang | Plus MathLang MathLang | Subtract MathLang MathLang | Negate MathLang | Lift Int | MV String | Equals MathLang MathLang
  deriving stock (Eq, Ord)

instance Num MathLang where
  fromInteger = Lift . fromInteger
  (+) = Plus
  (-) = Subtract
  (*) = Times
  negate = Negate

instance IsString MathLang where
  fromString = MV

instance Show MathLang where
  show a = showString "$" . showsPrec 0 a . showString "$" $ ""
  showsPrec n (Times a b) = showParen (n > 5) $ showsPrec 5 a . showString "  \\times " . showsPrec 5 b
  showsPrec n (Plus a b) = showParen (n > 4) $ showsPrec 4 a . showString " + " . showsPrec 4 b
  showsPrec n (Subtract a b) = showParen (n > 4) $ showsPrec 4 a . showString " - " . showsPrec 5 b
  showsPrec _ (Negate a) = showString " - " . showsPrec 10 a
  showsPrec n (Lift i) = showsPrec n i
  showsPrec _ (MV s) = showString s
  showsPrec n (Equals a b) = showParen (n > 0) $ showsPrec 0 a . showString "  = " . showsPrec 0 b

instance ToDot MathLang where
  toDot (Times a b) =
    makeTree "&times;" [a, b]
  toDot (Plus a b) = do
    makeTree "+" [a, b]
  toDot (Subtract a b) = do
    makeTree "-" [a, b]
  toDot (Equals a b) = do
    makeTree "=" [a, b]
  toDot (Negate a) = do
    makeTree "-" [a]
  toDot (Lift n) = newNode $ show n
  toDot (MV n) = newNode n


asMath :: MathLang -> MathLang
asMath = id


