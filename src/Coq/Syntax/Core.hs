{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Coq.Syntax.Core where

import Data.String
import GHC.Read

newtype Identifier = ID { fromID :: String }
  deriving (Eq,Ord,IsString)
instance Read Identifier where
  readPrec = fmap ID readPrec
instance Show Identifier where
  showsPrec i (ID s) = showsPrec i s
