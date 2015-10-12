
module KnotSpec.Syntax.Core where

import GHC.Read

newtype NameRoot = NR { fromNR :: String }
  deriving (Eq,Ord)
instance Read NameRoot where
  readPrec = fmap NR readPrec
instance Show NameRoot where
  showsPrec i (NR s) = showsPrec i s

type Suffix     = String
type CtorName   = String
type LookupName = String
type FunName    = String

-- newtype TypeName = TN { fromTN :: String }
--   deriving (Eq,Ord)
-- instance Read TypeName where
--   readPrec = fmap TN readPrec
-- instance Show TypeName where
--   showsPrec i (TN s) = showsPrec i s
