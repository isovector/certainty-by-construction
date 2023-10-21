module Dot where

import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe (fromMaybe)
import Data.Bool (bool)
import Data.List (group, intercalate)
import Data.Char (isAlphaNum)
import System.Process (callProcess)
import Data.Foldable (for_, foldrM, toList)
import Types
import Data.List.NonEmpty (NonEmpty (..))


newtype DotM a = DotM
  { unDotM :: StateT Int (Writer [String]) a
  }
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadState Int
    , MonadWriter [String]
    )

instance Show (DotM a) where
  show _ = "A tree"

instance ToDot Ctor where
  toDot (Ctor s) = ctorNode s
  toDot (FakeCtor s) = newNode s

instance ToDot Trie where
  toDot (Table 1) = shapedNode "square" "&#9632;"
  toDot (Table n) = tableNode $ show n : replicate n "&#9632;"
  toDot (Or t1 t2) = do
    me <- shapedNode "circle" ""
    n1 <- toDot t1
    n2 <- toDot t2
    addEdge me n1
    addEdge me n2
    pure me
  toDot (And n t) = do
    me <- tableNode $ show n : replicate n " "
    ns <- replicateM n $ toDot t
    for_ (zip [1 .. n] ns) $ \(ix, n) -> addEdge (SubNode me ix) n
    pure me

compile :: String -> Schema -> DotM Node
compile lbl = cluster (Just lbl) . toDot . Beside . go
  where
    go s =
      case s of
        SPlus scs -> scs >>= go
        STimes ctor es -> pure $ do
          ns <- traverse (shapedNode "rect" . showType) es
          me <- toDot ctor
          for_ ns $ addEdge me
          pure me
        -- TODO(sandy): bug. this should have a type box
        SList es -> pure $ toDot $ fmap showType es

showType :: Either String Metavar -> String
showType (Left s) = s
showType (Right me) = show me

instance ToDot a => ToDot (Beside a) where
  toDot (Beside ls) = do
    foldr1 f
      $ fmap (cluster Nothing)
      $ fmap toDot ls
    where
      f l r = do
        ln <- toDot l
        rn <- toDot r
        sameRank [ln, rn]
        pure rn


instance (ToDot a, ToDot b) => ToDot (GoesTo a b) where
  toDot (GoesTo lbl l r) = do
    ln <- cluster Nothing $ toDot l
    larr <- invisNode
    rarr <- invisNode
    addLabeledEdge lbl larr rarr
    rn <- cluster Nothing $ toDot r
    sameRank [ln, larr, rarr, rn]
    pure rn
  toDot (Cons lbl l r) = do
    ln <- cluster Nothing $ toDot l
    larr <- invisNode
    rarr <- invisNode
    addLabeledEdge lbl larr rarr
    rn <- toDot r
    sameRank [ln, larr, rarr, rn]
    pure rn

instance ToDot a => ToDot (Rose a) where
  toDot (Pure a) = toDot a
  toDot (Rose ros) = do
    ns <- traverse toDot ros
    me <- ctorNode "&otimes;"
    for_ ns $ addEdge me
    pure me

instance ToDot a => ToDot (LRose a) where
  toDot (LPure a) = toDot a
  toDot (LRose a ros) = do
    ns <- traverse toDot ros
    me <- toDot a
    for_ ns $ addEdge me
    pure me

instance ToDot a => ToDot (Bin a) where
  toDot (L a) = toDot a
  toDot (Br l r) = do
    nl <- toDot l
    nr <- toDot r
    me <- ctorNode "Br"
    addEdge me nl
    addEdge me nr
    pure me

instance ToDot a => ToDot (Search a) where
  toDot Empty = ctorNode "Empty"
  toDot (Split a l r) = do
    nl <- toDot l
    nr <- toDot r
    me <- toDot a
    addEdge me nl
    addEdge me nr
    pure me

instance {-# OVERLAPPING #-} ToDot String where
  toDot = newNode

instance ToDot Int where
  toDot = newNode . show

instance ToDot Bool where
  toDot = newNode . show

instance ToDot Float where
  toDot = newNode . show

instance ToDot Double where
  toDot = newNode . show

instance ToDot a => ToDot [a] where
  toDot [] = ctorNode "Nil"
  toDot (a : as) = do
    n <- toDot as
    me <- toDot a
    addEdge me n
    pure me

instance ToDot a => ToDot (NonEmpty a) where
  toDot = go . toList
    where
      go [] = error "impossible"
      go [a] = toDot a
      go (a : as) = do
        n <- go as
        me <- toDot a
        addEdge me n
        pure me

instance Show a => ToDot (Focused a) where
  toDot (Focused a) = do
    cluster Nothing $ do
      pointer <- invisNode
      n <- newNode $ show a
      addEdge pointer n
      sameRank [pointer, n]
      pure n
  toDot (Unfocused a) = newNode $ show a

instance ToDot Metavar where
  toDot = newNode . show


preamble :: [String]
preamble =
  [ "digraph g {"
  , "bgcolor=\"transparent\";"
  , "compound=true;"
  , "newrank=true;"
  , "splines=polyline;"
  ]

runDotM :: DotM a -> String
runDotM
  = unlines
  . (join preamble :)
  . (++ ["}"])
  . snd
  . runWriter
  . flip evalStateT 0
  . unDotM


class ToDot a where
  toDot :: a -> DotM Node

instance ToDot (DotM Node) where
  toDot = id


data Node = Node Int | SubNode Node Int
  deriving stock (Eq, Ord, Show)


nodeName :: Node -> String
nodeName (Node n) = ('n' :) $ show n
nodeName (SubNode n f) = nodeName n ++ ":f" ++ show f


fresh :: DotM Int
fresh = get <* modify' (+ 1)

newNode :: String -> DotM Node
newNode "" = shapedNode "point" ""
newNode label = shapedNode "oval" label


tableNode :: [String] -> DotM Node
tableNode cols = do
  n <- fmap Node get
  modify' (+ 1)
  let label = intercalate "|" $ zipWith (\ix l -> mconcat ["<f", show ix, "> ", l]) [0..] cols
  tell $ pure $ nodeName n <> "[shape=\"record\";label=" ++ show label ++ "]"
  pure n

ctorNode :: String -> DotM Node
ctorNode = shapedNode "invhouse"


invisNode :: DotM Node
invisNode = do
  n <- fmap Node get
  modify' (+ 1)
  tell $ pure $ nodeName n <> "[style=\"invis\";width=0.01]"
  pure n

shapedNode :: String -> String -> DotM Node
shapedNode shape label = do
  n <- fmap Node get
  modify' (+ 1)
  tell $ pure $ nodeName n <> "[shape=" <> show shape <> ";label=" <> show label <> "]"
  pure n


sameRank :: [Node] -> DotM ()
sameRank ns = do
  tell $ pure "{ rank=same; "
  for_ ns $ tell . pure . (<> ";") . nodeName
  tell $ pure "}"


cluster :: Maybe String -> DotM a -> DotM a
cluster label m = do
  name <- fmap (show . (+ (length $ show label))) fresh
  tell $ pure $ "subgraph cluster" <> name <> " {"
  tell $ pure $ "label = " <> maybe (show "") show label <> ";"
  r <- m
  tell $ pure "}"
  pure r


addEdge :: Node -> Node -> DotM ()
addEdge n1 n2 = do
  tell $ pure $ nodeName n1 <> " -> " <> nodeName n2


addLabeledEdge :: String -> Node -> Node -> DotM ()
addLabeledEdge lbl n1 n2 = do
  tell $ pure $ nodeName n1 <> " -> " <> nodeName n2 <> "[label=" <> show lbl <> "]"


__design
    :: (ToDot a, Show a)
    => (String, [String], [(String, String)])
    -> String
    -> String
    -> a
    -> IO ()
__design (name, _, kvs) _ hash a = do
  let fp = hash <> ".png"
      label = fromMaybe (show a) $ lookup "label" kvs
      figname = bool name ("fig:" <> __makeFigName (show label))  $ name == ""

  writeFile "/tmp/output.dot" $ runDotM $ toDot a

  callProcess "dot"
    [ "-Tpng"
    , "-Gdpi=300"
    , "-o/tmp/out.png"
    , "/tmp/output.dot"
    ]
  callProcess "convert"
    [ "/tmp/out.png"
    , "-density"
    , "300"
    , "-units"
    , "pixelsperinch"
    , "-resize"
    , "40%"
    , fp
    ]

  putStrLn $
    mconcat ["![", label, "](", fp, "){#", figname , "}"]


__makeFigName :: String -> String
__makeFigName
    = concatMap (\x -> bool x (take 1 x) $ take 1 x == "_")
    . group
    . fmap go
  where
    go c | isAlphaNum c = c
    go _ = '_'

instance ToDot Char where
  toDot = newNode . pure

makeTree :: ToDot a => String -> [a] -> DotM Node
makeTree s as = do
  n <- newNode s
  ns <- traverse toDot as
  foldrM (\a n' -> addEdge n' a >> pure n') n ns

makeLabeledTree :: ToDot a => String -> [(String, a)] -> DotM Node
makeLabeledTree s (unzip -> (lbs, as)) = do
  n <- newNode s
  ns <- traverse toDot as
  foldrM (\(lbl, a) n' -> addLabeledEdge lbl n' a >> pure n') n $ zip lbs ns



