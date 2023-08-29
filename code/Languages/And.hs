module Languages.And where

import Dot
import Types

data AndLang = Y | N | A AndLang AndLang | MV Metavar | AnyContext AndLang
  deriving stock (Eq, Ord)

instance Show AndLang where
  showsPrec _ Y = showString "Y"
  showsPrec _ N = showString "N"
  showsPrec _ (MV m) = showString $ show m
  showsPrec p (A l r) = showParen (p /= 0) $ showsPrec 10 l . showString "A" . showsPrec 10 r
  showsPrec p (AnyContext a) = showParen (p /= 0) $ showString "... " . showsPrec 10 a

instance ToDot AndLang where
  toDot Y = newNode "Y"
  toDot N = newNode "N"
  toDot (MV m) = newNode $ show m
  toDot (A l r) = do
    ln <- toDot l
    a <- newNode "A"
    rn <- toDot r
    addEdge a ln
    addEdge a rn
    pure a
  toDot (AnyContext l) = do
    a <- newNode "&hellip;"
    ln <- toDot l
    addEdge a ln
    pure a

