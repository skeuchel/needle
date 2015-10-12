{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-unused-binds #-}

module KnotSpec.Parser (Parser, pSpecification) where

import Control.Applicative
import Control.Monad (msum)
import Data.List

import qualified Text.Parsec as P
import qualified Text.Parsec.Language as P
import qualified Text.Parsec.Token as P

import KnotSpec.Syntax

-- Keep this alphabetically sorted
theReservedNames :: [String]
theReservedNames = [ "env"
                   , "fun"
                   , "namespace"
                   , "relation"
                   , "shift"
                   , "sort"
                   , "subst"
                   , "weaken"
                   ]

isReservedName :: String -> Bool
isReservedName name = scan theReservedNames
  where
    scan :: [String] -> Bool
    scan []     = False
    scan (r:rs) = case compare r name of
                    LT -> scan rs
                    EQ -> True
                    GT -> False

P.TokenParser{..} =
  P.makeTokenParser $ P.haskellStyle
    { P.opStart         = P.oneOf ":!#$%&*+./<=>?@\\^|-~,"
    , P.opLetter        = P.oneOf ":!#$%&*+./<=>?@\\^|-~,"
    , P.reservedNames   = theReservedNames
    , P.reservedOpNames = [ ":", ":=", "|", "+", "=", "->" ]
    }


type Parser a = P.Parsec String () a

--  __  __     _
-- |  \/  |___| |_ __ _ _ _  __ _ _ __  ___ ___
-- | |\/| / -_)  _/ _` | ' \/ _` | '  \/ -_|_-<
-- |_|  |_\___|\__\__,_|_||_\__,_|_|_|_\___/__/

nameRootLetter :: String
nameRootLetter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

suffixLetter :: String
suffixLetter = "'_0123456789₀₁₂₃₄₅₆₇₈₉"

pNameRoot :: Parser NameRoot
pNameRoot = NR <$> lexeme (some (P.oneOf nameRootLetter))

pTypeName :: Parser TypeName
pTypeName = TN <$> identifier

pName :: Parser Name
pName =
  lexeme . P.try $
    do
      nameRoot <- some (P.oneOf nameRootLetter)
      if isReservedName nameRoot
        then P.unexpected ("reserved word " ++ nameRoot)
        else (,) (NR nameRoot) <$> many (P.oneOf suffixLetter)

--  ___              _  __ _         _   _
-- / __|_ __  ___ __(_)/ _(_)__ __ _| |_(_)___ _ _
-- \__ \ '_ \/ -_) _| |  _| / _/ _` |  _| / _ \ ' \
-- |___/ .__/\___\__|_|_| |_\__\__,_|\__|_\___/_||_|
--     |_|

pSpecification :: Parser TermSpec
pSpecification =
  do
    whiteSpace
    decls <- many pDecl
    P.eof
    let (nds,sds,fds,eds,rds) = partitionDecls decls
    return $ TermSpec nds sds fds eds rds

data Decl
  = ND NamespaceDecl
  | SD SortDecl
  | FD FunDecl
  | ED EnvDecl
  | RD RelationDecl

partitionDecls :: [Decl] -> (NamespaceDecls,SortDecls,FunDecls,EnvDecls,RelationDecls)
partitionDecls = go [] [] [] [] []
  where go nds sds fds eds rds []     = (sort nds, sort sds, sort fds, sort eds, sort rds)
        go nds sds fds eds rds (d:ds) =
          case d of
            ND nd -> go (nd:nds) sds fds eds rds ds
            SD sd -> go nds (sd:sds) fds eds rds ds
            FD fd -> go nds sds (fd:fds) eds rds ds
            ED ed -> go nds sds fds (ed:eds) rds ds
            RD rd -> go nds sds fds eds (rd:rds) ds

pDecl :: Parser Decl
pDecl =
      ND <$> pNamespaceDecl
  <|> SD <$> pSortDecl
  <|> FD <$> pFunDecl
  <|> ED <$> pEnvDecl
  <|> RD <$> pRelationDecl

--  _  _
-- | \| |__ _ _ __  ___ ____ __  __ _ __ ___ ___
-- | .` / _` | '  \/ -_|_-< '_ \/ _` / _/ -_|_-<
-- |_|\_\__,_|_|_|_\___/__/ .__/\__,_\__\___/__/
--                        |_|

pNamespaceDecl :: Parser NamespaceDecl
pNamespaceDecl =
  NamespaceDecl
    <$  reserved "namespace"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*  colon
    <*> pTypeName
    <*> many pNamespaceDirective

pNamespaceDirective :: Parser NamespaceDirective
pNamespaceDirective =
  reservedOp "-" >>
  msum
    [ NamespaceShift
        <$  reserved "shift"
        <*  colon
        <*> stringLiteral
    , NamespaceSubst
        <$  reserved "subst"
        <*  colon
        <*> stringLiteral
    , NamespaceWeaken
        <$  reserved "weaken"
        <*  colon
        <*> stringLiteral
    , NamespaceCutoff
        <$  reserved "cutoff"
        <*  colon
        <*> stringLiteral
    ]

--  ___          _
-- / __| ___ _ _| |_ ___
-- \__ \/ _ \ '_|  _(_-<
-- |___/\___/_|  \__/__/

pSortDecl :: Parser SortDecl
pSortDecl =
  SortDecl
    <$  reserved "sort"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*  reservedOp ":="
    <*> many pCtorDecl

pCtorDecl :: Parser CtorDecl
pCtorDecl =
    CtorVar
      <$  reservedOp "+"
      <*> identifier
      <*> pName
  <|>
    CtorTerm
      <$  reservedOp "|"
      <*> identifier
      <*> many pFieldDecl

pFieldDeclPrim :: Parser FieldDecl
pFieldDeclPrim =
  FieldDecl
    <$> (brackets (commaSep1 pVleItem) <|> return [])
    <*> pName

pFieldDecl :: Parser FieldDecl
pFieldDecl = parens pFieldDeclPrim <|> pFieldDeclPrim

--  ___ _         _
-- | _ |_)_ _  __| |____ __  ___ __ ___
-- | _ \ | ' \/ _` (_-< '_ \/ -_) _(_-<
-- |___/_|_||_\__,_/__/ .__/\___\__/__/
--                    |_|

pVleItem :: Parser VleItem
pVleItem =
      do
         n@(i,s) <- pName
         VleCall (fromNR i ++ s) <$> pName <|> return (VleBinding n)
  <|> VleCall <$> identifier <*> pName

pVle :: Parser Vle
pVle = braces (return []) <|> commaSep1 pVleItem

--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _  ___
-- | _| || | ' \/ _|  _| / _ \ ' \(_-<
-- |_| \_,_|_||_\__|\__|_\___/_||_/__/

pFunDecl :: Parser FunDecl
pFunDecl =
  FunDecl
    <$  reserved "fun"
    <*> identifier  -- pFunName
    <*  colon
    <*> pTypeName
    <*  reservedOp "->"
    <*> brackets (commaSep1 pTypeName)
    <*> some pFunCase

pFunCase :: Parser FunCase
pFunCase =
  FunCase
    <$  reservedOp "|"
    <*> identifier -- pCtorName
    <*> many pName
    <*  reservedOp "->"
    <*> pVle

--  ___         _                            _
-- | __|_ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | _|| ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

pEnvDecl :: Parser EnvDecl
pEnvDecl =
  EnvDecl
    <$  reserved "env"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*  reservedOp ":="
    <*> many pEnvCtor

pEnvCtor :: Parser EnvCtor
pEnvCtor =
  EnvCtorNil
    <$  reservedOp "+"
    <*> identifier    -- pCtorName
  <|>
  EnvCtorCons
    <$  reservedOp "|"
    <*> identifier    -- pCtorName
    <*  colon
    <*> pName
    <*  reservedOp "->"
    <*> many pName

--  ___     _      _   _
-- | _ \___| |__ _| |_(_)___ _ _  ___
-- |   / -_) / _` |  _| / _ \ ' \(_-<
-- |_|_\___|_\__,_|\__|_\___/_||_/__/

pMbEnv :: Parser MbTypeName
pMbEnv = Just <$> brackets pTypeName <|> return Nothing

pRelationDecl :: Parser RelationDecl
pRelationDecl =
  RelationDecl
    <$  reserved "relation"
    <*> pMbEnv
    <*> pTypeName
    <*> many pTypeName
    <*  reservedOp ":="
    <*> many pRule

pRule :: Parser Rule
pRule =
  Rule
    <$  reservedOp "|"
    <*> identifier
    <*  reservedOp ":"
    <*> many (P.try $ pFormula <* reservedOp "->")
    <*> pJudgement
    <*> pMbRuleBindings

pRuleBinding :: Parser RuleBinding
pRuleBinding =
  RuleBinding
    <$> pName
    <*  reservedOp "->"
    <*> commaSep1 pSymbolicTerm

pMbRuleBindings :: Parser RuleBindings
pMbRuleBindings =
  brackets (commaSep1 pRuleBinding) <|> return []

pFormula :: Parser Formula
pFormula =
      FormBinding <$> braces pRuleBinding
  <|> FormJudgement <$> pMbRuleBindings <*> pJudgement

pJudgement :: Parser Judgement
pJudgement =
  Judgement
    <$> pTypeName
    <*> many pSymbolicTerm

pSymbolicTerm :: Parser SymbolicTerm
pSymbolicTerm =
      braces (SymCtorVar <$> identifier <*> pName)
  <|> parens (SymCtorTerm <$> identifier <*> many pSymbolicTerm)
  <|> SymVar <$> pName
