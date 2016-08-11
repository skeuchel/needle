{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Coq.Pretty.Common  where

import Control.Applicative (Applicative)
import Control.Monad.Reader
import System.IO

import qualified Text.PrettyPrint.ANSI.Leijen as P

--------------------------------------------------------------------------------

-- Pretty printing monad. It keeps some pretty
-- printing information in an environment.
newtype DocM s a = DocM { unDocM :: Reader s a }
  deriving (Applicative, Functor, Monad)

instance MonadReader s (DocM s) where
  ask              = DocM ask
  local f (DocM m) = DocM $ local f m

runDocM :: DocM s a -> s -> a
runDocM = runReader . unDocM

getEnv :: DocM s s
getEnv = DocM ask

--------------------------------------------------------------------------------

-- The environment.
type Indent = Int
data PPMode =
  PPMode {
    bulletIndent  :: Indent,
    matchIndent   :: Indent,
    scriptIndent  :: Indent,
    onsideIndent  :: Indent,
    spacing       :: Bool,
    comments      :: Bool
  }

defaultMode :: PPMode
defaultMode = PPMode {
  bulletIndent  = 2,
  matchIndent   = 2,
  scriptIndent  = 2,
  onsideIndent  = 2,
  spacing       = True,
  comments      = True
  }

-- Our specific instance.
type Doc = DocM PPMode P.Doc

putDoc :: Doc -> IO ()
putDoc dm = P.putDoc $ (runDocM dm) defaultMode

hPutDoc :: Handle -> Doc -> IO ()
hPutDoc h dm = P.hPutDoc h $ (runDocM dm) defaultMode

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

infixr 5 <$$>

(<$$>) :: Doc -> Doc -> Doc
am <$$> bm =
  do
    a <- am
    b <- bm
    return (a P.<$> b)

indent :: Int -> Doc -> Doc
indent = liftM . P.indent

tupled :: [Doc] -> Doc
tupled = parenList

dot :: Doc
dot = char '.'

class Pretty a where
  -- | Pretty-print something in isolation.
  pretty :: a -> Doc
  -- | Pretty-print something in a precedence context.
  prettyPrec :: Int -> a -> Doc
  pretty = prettyPrec 0
  prettyPrec _ = pretty
  lpretty :: [a] -> [Doc]
  lpretty = map pretty
  hpretty :: [a] -> Doc
  hpretty = hsep . lpretty
  vpretty :: [a] -> Doc
  vpretty = vsep . lpretty

-- The pretty printing combinators

empty :: Doc
empty = return P.empty

nest :: Int -> Doc -> Doc
nest = liftM . P.nest

line :: Doc
line = return P.line

-- Literals

text, ptext :: String -> Doc
text = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

int :: Int -> Doc
int = return . P.int

-- Simple Combining Forms
parens, brackets, braces,squotes,dquotes :: Doc -> Doc
parens       = liftM P.parens
brackets     = liftM P.brackets
braces       = liftM P.braces
squotes      = liftM P.squotes
dquotes      = liftM P.dquotes

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

-- Constants

semi,comma,colon,space,equals :: Doc
semi = return P.semi
comma = return P.comma
colon = return P.colon
space = return P.space
equals = return P.equals

lparen,rparen,lbrace,rbrace :: Doc
lparen = return  P.lparen
rparen = return  P.rparen
lbrace = return  P.lbrace
rbrace = return  P.rbrace

-- Combinators

(<>),(<+>),($$){-,($+$)-} :: Doc -> Doc -> Doc
aM <> bM = do{a<-aM;b<-bM;return (a P.<> b)}
aM <+> bM = do{a<-aM;b<-bM;return (a P.<+> b)}
aM $$ bM = do{a<-aM;b<-bM;return (P.align (a P.<$> b))}

{-
vsep :: [Doc] -> Doc
vsep = fold (<$>)
  where  fold f []       = empty
         fold f ds       = foldr1 f ds
-}

hcat,hsep,vcat,sep,cat,fsep,fcat,vsep,list :: [Doc] -> Doc
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vsep dl = sequence dl >>= return . P.vsep
vcat dl = sequence dl >>= return . P.vcat
sep dl = sequence dl >>= return . P.sep
cat dl = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fillSep
fcat dl = sequence dl >>= return . P.fillCat
list dl = sequence dl >>= return . P.list

-- Some More
hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do{d<-dM;r<-rM;return $ P.sep [d, P.nest i r]}

-- Yuk, had to cut-n-paste this one from Pretty.hs
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []     = []
punctuate p (d1:ds) = go d1 ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es

punctuate' :: Doc -> [Doc] -> [Doc]
punctuate' _ []     = []
punctuate' p (d1:ds) = go d1 ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <+> p) : go e es

parenList :: [Doc] -> Doc
parenList = parens . hsep . punctuate comma

braceList :: [Doc] -> Doc
braceList = braces . hsep . punctuate comma

bracketList :: [Doc] -> Doc
bracketList = brackets . hsep

-- Monadic PP Combinators -- these examine the env
blankline :: Doc -> Doc
blankline dl =
  do
    e <- getEnv
    if spacing e
      then space $$ dl
      else dl

mySep :: [Doc] -> Doc
mySep [x]    = x
mySep (x:xs) = x <+> fsep xs
mySep []     = error "Internal error: mySep"

-- same, except that continuation lines are indented,
-- which is necessary to avoid triggering the offside rule.
myFSep :: [Doc] -> Doc
myFSep [] = empty
myFSep (d:ds) =
  do
    e <- getEnv
    let n = onsideIndent e
    nest n (hsep (nest (-n) d:ds))

showWidth :: Int -> Doc -> String
showWidth w dm = P.displayS (P.renderPretty 0.4 w (runDocM dm defaultMode)) ""

-- nestBullet :: Doc -> Doc
-- nestBullet m =
--   doc
--       e <- getEnv
