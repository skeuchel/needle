{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module KnotSpec.Parser (Parser, pSpecification) where

import           KnotSpec.Syntax

import qualified Text.Parsec as P
import qualified Text.Parsec.Language as P
import qualified Text.Parsec.Token as P

import           Control.Applicative
import           Control.Monad (msum)
import           Data.Foldable (asum)
import           Data.Monoid ((<>))

-- Keep this alphabetically sorted
theReservedNames :: [String]
theReservedNames =
  [ "env"
  , "fun"
  , "namespace"
  , "relation"
  , "set"
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

tokenParser :: P.TokenParser ()
tokenParser =
  P.makeTokenParser $ P.haskellStyle
    { P.opStart         = P.oneOf ":!#$%&*+./<=>?@\\^|-~,"
    , P.opLetter        = P.oneOf ":!#$%&*+./<=>?@\\^|-~,"
    , P.reservedNames   = theReservedNames
    , P.reservedOpNames = [ ";", ":", ":=", "|", "+", "=", "->" ]
    , P.identStart      = P.letter   <|> P.oneOf "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩαβγδεζηθικλμνξοπρστυφχψω"
    , P.identLetter     = P.alphaNum <|> P.oneOf "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩαβγδεζηθικλμνξοπρστυφχψω" <|> P.oneOf "_'"
    }

reserved = P.reserved tokenParser
commaSep1 = P.commaSep1 tokenParser
parens = P.parens tokenParser
braces = P.braces tokenParser
reservedOp = P.reservedOp tokenParser
brackets = P.brackets tokenParser
comma = P.comma tokenParser
colon = P.colon tokenParser
identifier = P.identifier tokenParser
stringLiteral = P.stringLiteral tokenParser
whiteSpace = P.whiteSpace tokenParser
lexeme = P.lexeme tokenParser

type Parser a = P.Parsec String () a

pLoc :: Parser Loc
pLoc = do
  pos <- P.getPosition
  return
    Loc
    { line = P.sourceLine pos
    , column = P.sourceColumn pos - 1
    }

toSnocList :: [a] -> SnocList a
toSnocList = foldl (:.) Nil

--  __  __     _
-- |  \/  |___| |_ __ _ _ _  __ _ _ __  ___ ___
-- | |\/| / -_)  _/ _` | ' \/ _` | '  \/ -_|_-<
-- |_|  |_\___|\__\__,_|_||_\__,_|_|_|_\___/__/

nameRootLetter :: String
nameRootLetter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyzΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩαβγδεζηθικλμνξοπρστυφχψω"

suffixLetter :: String
suffixLetter = "'_0123456789₀₁₂₃₄₅₆₇₈₉"

pNameRoot :: Parser NameRoot
pNameRoot = NR <$> pLoc <*> lexeme (some (P.oneOf nameRootLetter))

pTypeName :: Parser RawTypeName
pTypeName = RawTN <$> pLoc <*> identifier

pVariable :: Parser (RawVariable 'Parsed)
pVariable =
  lexeme . P.try $
    do
      loc <- pLoc
      ident <- some (P.oneOf nameRootLetter)
      if isReservedName ident
        then P.unexpected ("reserved word " <> ident)
        else RawVarParsed
               <$> pure (NR loc ident)
               <*> many (P.oneOf suffixLetter)
               <*> pure Nothing

pTypedVariable :: Parser (RawVariable 'Parsed)
pTypedVariable = do
  v@(RawVarParsed nr suf _) <- pVariable
  asum
    [ RawVarParsed nr suf . Just <$ colon <*> pTypeName
    , pure v
    ]

--  ___              _  __ _         _   _
-- / __|_ __  ___ __(_)/ _(_)__ __ _| |_(_)___ _ _
-- \__ \ '_ \/ -_) _| |  _| / _/ _` |  _| / _ \ ' \
-- |___/ .__/\___\__|_|_| |_\__\__,_|\__|_\___/_||_|
--     |_|

pSpecification :: Parser (TermSpec 'Parsed)
pSpecification =
  TermSpecRaw
    <$  whiteSpace
    <*> many pDecl
    <*  P.eof

pDecl :: Parser (Decl 'Parsed)
pDecl =
      ND <$> pNamespaceDecl
  <|> SD <$> pSortDecl
  <|> FD <$> pFunDecl
  <|> ED <$> pEnvDecl
  <|> ZD <$> pSetDecl
  <|> RD <$> pRelationDecl

--  _  _
-- | \| |__ _ _ __  ___ ____ __  __ _ __ ___ ___
-- | .` / _` | '  \/ -_|_-< '_ \/ _` / _/ -_|_-<
-- |_|\_\__,_|_|_|_\___/__/ .__/\__,_\__\___/__/
--                        |_|

pNamespaceDecl :: Parser (NamespaceDecl 'Parsed)
pNamespaceDecl =
  NamespaceDecl
    <$> pLoc
    <*  reserved "namespace"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*> (Just <$ colon <*> pTypeName <|> pure Nothing)
    <*> many pNamespaceDirective
    <*> pLoc

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

pSortDecl :: Parser (SortDecl 'Parsed)
pSortDecl =
  SortDecl
    <$  reserved "sort"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*  reservedOp ":="
    <*> many pCtorDecl

pCtorName :: Parser CtorName
pCtorName = CN <$> pLoc <*> identifier

pCtorDecl :: Parser (CtorDecl 'Parsed)
pCtorDecl =
    CtorVar
      <$  reservedOp "+"
      <*> pCtorName
      <*> braces pTypedVariable
  <|>
    CtorReg
      <$  reservedOp "|"
      <*> pCtorName
      <*> many (pFieldDecl SWMV)

pFieldDecl :: SWithMV w -> Parser (FieldDecl w 'Parsed 'Parsed)
pFieldDecl w = asum
  [ FieldDeclRaw
      <$> pLoc
      <*> (toSnocList <$> (brackets (commaSep1 pBindSpecItem) <|> pure []))
      <*> pVariable
  , parens $
    FieldDeclRaw
      <$> pLoc
      <*> (toSnocList <$> (brackets (commaSep1 pBindSpecItem) <|> pure []))
      <*> pTypedVariable
  , case w of
      SWMV -> braces $
              FieldDeclReference
                <$> pLoc
                <*> pTypedVariable
      SWOMV -> empty
  ]

--  ___ _         _
-- | _ |_)_ _  __| |____ __  ___ __ ___
-- | _ \ | ' \/ _` (_-< '_ \/ -_) _(_-<
-- |___/_|_||_\__,_/__/ .__/\___\__/__/
--                    |_|

pBindSpecItem :: Parser (BindSpecItem 'Parsed)
pBindSpecItem =
  asum
  [ do
      n@(RawVarParsed nr s _) <- pVariable
      BsiCall (FN (nrLoc nr) (nrId nr <> s))
        <$> pVariable <|> pure (BsiBinding n)
  , BsiCall <$> pFunName <*> pVariable
  ]

pBindSpec :: Parser (BindSpec 'Parsed)
pBindSpec = toSnocList <$> (braces (pure []) <|> commaSep1 pBindSpecItem)

--  ___             _   _
-- | __|  _ _ _  __| |_(_)___ _ _  ___
-- | _| || | ' \/ _|  _| / _ \ ' \(_-<
-- |_| \_,_|_||_\__|\__|_\___/_||_/__/

pFunName :: Parser FunName
pFunName = FN <$> pLoc <*> identifier

pFunDecl :: Parser (FunDecl 'Parsed)
pFunDecl =
  FunDecl
    <$  reserved "fun"
    <*> pFunName
    <*  colon
    <*> pTypeName
    <*  reservedOp "->"
    <*> brackets (commaSep1 pTypeName)
    <*> some pFunCase

pFunCase :: Parser (FunCase 'Parsed)
pFunCase =
  FunCase
    <$  reservedOp "|"
    <*> pCtorName
    <*> many (FunFieldRaw <$> pVariable)
    <*  reservedOp "->"
    <*> pBindSpec

--  ___         _                            _
-- | __|_ ___ _(_)_ _ ___ _ _  _ __  ___ _ _| |_ ___
-- | _|| ' \ V / | '_/ _ \ ' \| '  \/ -_) ' \  _(_-<
-- |___|_||_\_/|_|_| \___/_||_|_|_|_\___|_||_\__/__/

pEnvDecl :: Parser (EnvDecl 'Parsed)
pEnvDecl =
  EnvDecl
    <$  reserved "env"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*  reservedOp ":="
    <*> many pEnvCtorDecl

pEnvCtorDecl :: Parser (EnvCtorDecl 'Parsed)
pEnvCtorDecl =
  asum
  [ EnvCtorNil
    <$  reservedOp "+"
    <*> pCtorName
  , EnvCtorCons
    <$  reservedOp "|"
    <*> pCtorName
    <*  colon
    <*> pVariable
    <*  reservedOp "->"
    <*> many (pFieldDecl SWOMV)
    <*> asum
        [ Just <$ reservedOp ";" <*> pTypeName
        , pure Nothing
        ]
  ]

--  ___      _
-- / __| ___| |_ ___
-- \__ \/ -_)  _(_-<
-- |___/\___|\__/__/

pSetDecl :: Parser (SetDecl 'Parsed)
pSetDecl =
  SetDecl
    <$  reserved "set"
    <*> pTypeName
    <*  comma
    <*> commaSep1 pNameRoot
    <*  reservedOp ":="
    <*> many pSetCtorDecl

pSetCtorDecl :: Parser (SetCtorDecl 'Parsed)
pSetCtorDecl =
  SetCtor
    <$  reservedOp "|"
    <*> pCtorName
    <*> many pSetFieldDecl

pSetFieldDecl :: Parser (SetFieldDecl 'Parsed)
pSetFieldDecl =
  asum
  [ SetFieldDecl
      <$> pLoc
      <*> pVariable
  , parens $
    SetFieldDecl
      <$> pLoc
      <*> pTypedVariable
  ]

--  ___     _      _   _
-- | _ \___| |__ _| |_(_)___ _ _  ___
-- |   / -_) / _` |  _| / _ \ ' \(_-<
-- |_|_\___|_\__,_|\__|_\___/_||_/__/


pMbEnv :: Parser (Maybe RawTypeName)
pMbEnv = Just <$> brackets pTypeName <|> return Nothing

pRelationDecl :: Parser (RelationDecl 'Parsed)
pRelationDecl =
  RelationDecl
    <$  reserved "relation"
    <*> pMbEnv
    <*> pTypeName
    <*> many (pFieldDecl SWOMV)
    <*> many (comma *> pNameRoot)
    <*> many (reservedOp ";" *> pRelationOutput)
    <*  reservedOp ":="
    <*> many pRule

pRelationOutput :: Parser (FunName, RawTypeName)
pRelationOutput = (,) <$> pFunName <*  reservedOp "->" <*> pTypeName

pRule :: Parser (Rule 'Parsed)
pRule = asum
  [ RuleReg
    <$  reservedOp "|"
    <*> pCtorName
    <*> pure ()
    <*  reservedOp ":"
    <*> many (P.try $ pFormula <* reservedOp "->")
    <*> pJudgement
    <*> many (reservedOp ";" *> pRuleOutput)
  , (\cn rmb etn (fv,sfs) -> RuleVar cn rmb etn fv sfs)
    <$  reservedOp "+"
    <*> pCtorName
    <*> pure ()
    <*  reservedOp ":"
    <*> pure ()
    <*> braces
        ((,)
         <$> pVariable
         <*  reservedOp "->"
         <*> commaSep1 pSymbolicField
        )
    <*  reservedOp "->"
    <*> pJudgement
  ]

pRuleOutput :: Parser (FunName, RuleBindSpec 'Parsed)
pRuleOutput =
  (,)
    <$> pFunName
    <*  reservedOp "="
    <*> (braces (pure Nil)
         <|> toSnocList <$> commaSep1 pRuleBindSpecItem)

pFormula :: Parser (Formula 'Parsed)
pFormula =
      braces (
        FormLookup ()
          <$> pVariable
          <*  reservedOp "->"
          <*> commaSep1 pSymbolicField
      )
  <|> parens (do
        RawVarParsed nr suf _nothing <- pVariable
        reservedOp ":"
        rbs <- pRuleBindSpec
        jm@(Judgement rtn () _sts) <- pJudgement
        pure (FormJudgement
                (Just (RawVarParsed nr suf (Just rtn)))
                rbs jm ())
      )
  <|> FormJudgement Nothing
        <$> pRuleBindSpec
        <*> pJudgement
        <*> pure ()

pRuleBindSpec :: Parser (RuleBindSpec 'Parsed)
pRuleBindSpec =
  toSnocList <$> (brackets (commaSep1 pRuleBindSpecItem) <|> return [])

pRuleBindSpecItem :: Parser (RuleBindSpecItem 'Parsed)
pRuleBindSpecItem = parens pRuleBindSpecItem' <|> pRuleBindSpecItem'

-- TODO: left factorize / remove try
pRuleBindSpecItem' :: Parser (RuleBindSpecItem 'Parsed)
pRuleBindSpecItem' =
  P.try (RuleBsiBinding
         <$> pVariable
         <*  reservedOp "->"
         <*> (commaSep1 pSymbolicField <|> pure []))
  <|> RuleBsiCall <$> pFunName <*> pVariable

pJudgement :: Parser (Judgement 'Parsed)
pJudgement =
  Judgement
    <$> pTypeName
    <*> pure ()
    <*> many pSymbolicField

pSymbolicTerm :: Parser (SymbolicTerm 'Parsed)
pSymbolicTerm =
      braces (SymCtorVarRaw <$> pCtorName <*> pVariable)
  <|> parens (
          SymWeaken () ()
            <$  reserved "weaken"
            <*> pSymbolicTerm
            <*> ((Nil:.) . BsiBinding <$> pVariable
                 <|> toSnocList <$> parens (commaSep1 pBindSpecItem))
      <|> SymSubst ()
            <$  reserved "subst"
            <*> pVariable
            <*> pSymbolicTerm
            <*> pSymbolicTerm
      <|> SymCtorRegRaw
            <$> pCtorName
            <*> many pSymbolicField
      )
  <|> SymVar () <$> pVariable

pSymbolicField :: Parser (SymbolicField w 'Parsed)
pSymbolicField =
      SymFieldRawVar <$> pLoc <*> pVariable
  <|> SymFieldRawTerm <$> pLoc <*> pSymbolicTerm
