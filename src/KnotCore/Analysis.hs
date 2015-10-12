
module KnotCore.Analysis where

import KnotCore.Environment
import KnotCore.Syntax
import Data.Graph
import Data.List
import Data.Map (Map)
import qualified Data.Map as M

toNode :: FunDecl -> (FunDecl, FunName, [FunName])
toNode fd = (fd, fdName fd, nub $ sort fns)
  where fns = [ fn
              | fc  <- fdCases fd
              , VleCall {vleFunName = fn} <- fcRhs fc
              ]

makeFunGroup :: MESortGroupOfSort -> [FunDecl] -> FunGroupDecl
makeFunGroup meGroupOf fds =
    FunGroupDecl
      (funGroupName $ map fdName fds)
      sgtn
      (M.toList fgd')
  where
    fgd' :: Map SortTypeName [FunDecl]
    fgd' = M.fromListWith (++) [ (fdSource fd, [fd]) | fd <- fds ]
    stn  = fdSource $ head fds
    sgtn = M.findWithDefault undefined stn meGroupOf

analyze :: TermSpec -> TermSpec
analyze ts =
  let
    menvs  = metaEnvironments ts
    fdss :: [[FunDecl]]
    fdss = map flattenSCC $ stronglyConnComp
             [ toNode fd
             | fgd     <- tsFunGroupDecls ts
             , (_,fds) <- fgdFuns fgd
             , fd <- fds
             ]
    fgds :: [FunGroupDecl]
    fgds = map (makeFunGroup (meSortGroupOfSort menvs)) fdss
  in
    ts { tsFunGroupDecls = fgds }
