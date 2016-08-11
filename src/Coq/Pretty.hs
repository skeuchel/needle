{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-name-shadowing #-}

module Coq.Pretty (
  module Coq.Pretty.Common,
  module Coq.Pretty) where

import Coq.Pretty.Common
import Coq.Syntax

instance Pretty Identifier where
  pretty (ID s) = text s

instance Pretty Root where
  pretty (Root ss) =
    text "Require Import Coq.Program.Equality." <> line <>
    text "Require Import Coq.Program.Tactics." <> line <>
    text "Require Export Needle." <> line <>
    vpretty ss

instance Pretty Modifier where
  pretty ModNone = empty
  pretty ModLocal = text "Local"
  pretty ModGlobal = text "Global"

instance Pretty Sentence where
  pretty (SentenceDefinition def) = pretty def
  pretty (SentenceInductive ind) = pretty ind
  pretty (SentenceFixpoint fix) = pretty fix
  pretty (SentenceAssertionProof ass prf) =
    pretty ass <$$> pretty prf
  pretty (SentenceSection id phrs) =
    vsep
      [ text "Section" <+> pretty id <> char '.',
        indent 2 (vpretty phrs),
        text "End"  <+> pretty id <> char '.'
      ]
  pretty (SentenceOpaque id) =
    text "Opaque" <+> pretty id <> char '.'
  pretty (SentenceHint mod hint []) =
    fsep [ pretty mod
         , pretty hint
         ] <> char '.'
  pretty (SentenceHint mod hint dbs) =
    hsep ( pretty mod
         : pretty hint
         : char ':'
         : map pretty dbs
         ) <> char '.'
  pretty (SentenceScheme scheme) = pretty scheme
  pretty (SentenceCombinedScheme id ids) =
    hsep
      ([ text "Combined Scheme",
        pretty id,
        text "from"
       ] ++ punctuate comma (lpretty ids))
     <> char '.'
  pretty (SentenceBlankline) = empty
  pretty (SentenceArguments mod id args) =
    hsep $ [ pretty mod
           , text "Arguments"
           , pretty id
           ] ++
           lpretty args ++
           [ char '.'
           ]
  pretty (SentenceClassDecl cd) = pretty cd <> char '.'
  pretty (SentenceClassInst ci) = pretty ci <> char '.'
  pretty (SentenceVerbatim verbatim) = text verbatim
  pretty (SentenceContext binders) =
    hsep $ [text "Context"] ++ lpretty binders ++ [char '.']

instance Pretty Hint where
  pretty (HintResolve tms) =
    hsep (text "Hint Resolve" : lpretty tms)
  pretty (HintRewrite tms) =
    hsep (text "Hint Rewrite" : lpretty tms)
  pretty (HintRewriteRightToLeft tms) =
    hsep (text "Hint Rewrite <-" : lpretty tms)
  pretty (HintConstructors ids) =
    hsep (text "Hint Constructors" : lpretty ids)
  pretty (HintExtern lvl Nothing tac) =
    hsep [ text "Hint Extern"
         , text (show lvl)
         , text "=>"
         , pretty tac
         ]
  pretty (HintExtern lvl (Just pat) tac) =
    hsep [ text "Hint Extern"
         , text (show lvl)
         , parens (pretty pat)
         , text "=>"
         , pretty tac
         ]
instance Pretty PossiblyBracketedName where
  pretty (BracketedName name) = brackets (pretty name)
  pretty (BracedName name)    = braces (pretty name)
  pretty (NormalName name)    = pretty name

prettyType :: MbTerm -> [Doc]
prettyType Nothing   = []
prettyType (Just tm) = [colon, pretty tm]

prettyReturnType :: MbTerm -> [Doc]
prettyReturnType Nothing   = []
prettyReturnType (Just tm) = [text "return", pretty tm]

prettyMbAnnotation :: MbAnnotation -> [Doc]
prettyMbAnnotation Nothing   = []
prettyMbAnnotation (Just tm) = [pretty tm]

instance Pretty Annotation where
  pretty (Struct id) = braces (text "struct" <+> pretty id)

instance Pretty Definition where
  pretty (Definition id bds ty tm) =
    hsep
      ([ text "Definition", pretty id] ++
       lpretty bds ++ prettyType ty ++
       [ text ":=", pretty tm]) <> char '.'


instance Pretty Scheme where
  pretty (Scheme bodies) =
    vsep
      (zipWith (<+>)
         (text "Scheme" : repeat (text "with"))
         (lpretty bodies))
    <> char '.'

instance Pretty SchemeBody where
  pretty (SchemeInduction id ty) =
    hsep
    [ pretty id,
      text ":= Induction for",
      pretty ty,
      text "Sort",
      text "Prop"
    ]

instance Pretty Inductive where
  pretty (Inductive bodies) =
    vsep
      (zipWith (<+>)
         (text "Inductive" : repeat (text "with"))
         (lpretty bodies))
    <> char '.'

instance Pretty InductiveBody where
  pretty (InductiveBody id bds ty ctors) =
    hsep
      ([ pretty id ] ++
       lpretty bds ++
       [ char ':'
       , pretty ty
       , text ":="
       ]) <$$>
    indent 2 (vpretty ctors)

instance Pretty InductiveCtor where
  pretty (InductiveCtor id bds ty) =
    case ty of
      Just ty ->
        nest 4 $
        fsep [char '|', pretty id,
              fsep (lpretty bds ++ [colon, nest 4 (pretty ty)])
             ]
      Nothing ->
        nest 4 $
        fsep [char '|', pretty id,
              fsep (lpretty bds)
             ]

instance Pretty Fixpoint where
  pretty (Fixpoint bodies) =
    vsep
      (zipWith (<+>)
         (text "Fixpoint" : repeat (text "with"))
         (lpretty bodies))
    <> char '.'

instance Pretty FixpointBody where
  pretty (FixpointBody id bds mbAnno ty tm) =
    hsep
      ([ pretty id ] ++
       lpretty bds ++
       prettyMbAnnotation mbAnno ++
       [ char ':' ]
      ) <$$>
    hsep
      [ pretty ty
      , text ":="
      ] <$$>
    indent 2 (pretty tm)

instance Pretty Binder where
  pretty (BinderName nm) = pretty nm
  pretty (BinderNameType nms tm) =
    parens . hsep $ [hpretty nms, colon, pretty tm]
  pretty (BinderImplicitName nm) = braces (pretty nm)
  pretty (BinderImplicitNameType nms tm) =
    braces . hsep $ [hpretty nms, colon, pretty tm]

instance Pretty Name where
  pretty (NameIdent id) = pretty id
  pretty (NameUnderscore) = char '_'

instance Pretty QualId where
  pretty (Ident id) = pretty id

instance Pretty Term where
  pretty (TermApp fun args) =
    parens $ foldl (<+>) (pretty fun) (lpretty args)
  pretty (TermNum num) = text (show num)
  pretty (TermQualId id) = pretty id
  pretty (TermSort srt) = pretty srt
  pretty (TermMatch item mbTy eqns) =
    vsep
      [ hsep
          ([ text "match"
           , pretty item ] ++
           prettyReturnType mbTy ++
           [ text "with" ])
      , indent 2 (vpretty eqns)
      , text "end"
      ]
  pretty (TermFunction source target) =
    pretty source <+> text "->" <+> pretty target
  pretty (TermAbs bds tm) =  parens $
    hsep ([ text "fun" ] ++ lpretty bds ++ [ text "=>" ]) <$$>
    indent 2 (pretty tm)
  pretty (TermForall bds tm) = parens $
    hsep ([ text "forall" ] ++ lpretty bds ++ [ char ',' ]) <$$>
    indent 2 (pretty tm)
  pretty (TermAnd tms) = vsep (punctuate' (text "/\\") (lpretty tms))
  pretty (TermEq l r)  = parens (pretty l <+> char '=' <+> pretty r)
  pretty (TermLet id bds type_ rhs body) = parens $
    hsep ([text "let", pretty id]
          ++ lpretty bds
          ++ prettyType type_
          ++ [text ":=",
              pretty rhs,
              text "in"
             ]) <$$> pretty body
  pretty TermUnderscore = text "_"

instance Pretty MatchItem where
  pretty (MatchItem tm itemAs itemIn) =
     hsep . concat $
     [ [ pretty tm ]
     , maybe [] (\name -> [text "as", pretty name]) itemAs
     , maybe [] (\ty   -> [text "in", pretty ty]) itemIn
     ]

instance Pretty Equation where
  pretty (Equation pat body) =
    hsep [text "|", pretty pat, text "=>", pretty body]

instance Pretty Pattern where
  pretty (PatCtor id fields) =
    parens (hsep (pretty id : lpretty fields))
  pretty (PatCtorEx id fields) =
    parens (hsep (pretty id : lpretty fields))
  pretty (PatAtCtor id fields) =
    parens (hsep ((text "@" <> pretty id) : lpretty fields))
  pretty (PatAtCtorEx id fields) =
    parens (hsep ((text "@" <> pretty id) : lpretty fields))
  pretty (PatQualId id) =
    pretty id
  pretty (PatUnderscore) =
    text "_"

instance Pretty Sort where
  pretty (Prop) = text "Prop"
  pretty (Set)  = text "Set"
  pretty (Type) = text "Type"

instance Pretty Assertion where
  pretty (Assertion kw id bds ty) =
    vsep
      [ hsep
          [ pretty kw,
            pretty id,
            hpretty bds,
            colon
          ],
        indent 2 (pretty ty) <> char '.'
      ]

instance Pretty AssertionKeyword where
  pretty AssTheorem     = text "Theorem"
  pretty AssLemma       = text "Lemma"
  pretty AssRemark      = text "Remark"
  pretty AssFact        = text "Fact"
  pretty AssCorollary   = text "Corollary"
  pretty AssProposition = text "Proposition"
  pretty AssDefinition  = text "Definition"
  pretty AssExample     = text "Example"

instance Pretty Proof where
  pretty (ProofWith with steps) =
    vsep
      [ text "Proof with" <+> hsep (punctuate' (char ';') (lpretty with)) <+> char '.',
        indent 2 . vsep $ map (<> char '.') (lpretty steps),
        text "Defined."
      ]
  pretty (ProofDefined steps) =
    vsep
      [ text "Proof.",
        indent 2 . vsep $ map (<> char '.') (lpretty steps),
        text "Defined."
      ]
  pretty (ProofQed steps) =
    vsep
      [ text "Proof.",
        indent 2 . vsep $ map (<> char '.') (lpretty steps),
        text "Qed."
      ]

instance Pretty ProofStep where
  pretty (PrInduction id)         = text "induction" <+> pretty id
  pretty (PrMutualInduction id _) = text "apply_mutual_ind" <+> pretty id
  pretty (PrCrushInd)             = text "crush_ind"
  pretty (PrApply tm)             = text "apply" <+> parens (pretty tm)
  pretty (PrApplyIn tm id)        = text "apply" <+> parens (pretty tm) <+> text "in" <+> pretty id
  pretty (PrExact tm)             = text "exact" <+> parens (pretty tm)
  pretty (PrSeq steps)            = hsep (punctuate (char ';') (lpretty steps))
  pretty (PrIntros ids)           = hsep (text "intros":map pretty ids)
  pretty (PrRevert ids)           = hsep (text "revert":map pretty ids)
  pretty (PrTry step)             = text "try" <+> parens (pretty step)
  pretty (PrConstructor)          = text "constructor"
  pretty (PrAuto)                 = text "auto"
  pretty (PrFail)                 = text "fail"
  pretty (PrInversion id)         = text "inversion" <+> pretty id
  pretty (PrSubst)                = text "subst"
  pretty (PrSimpl)                = text "simpl"
  pretty (PrRepeat step)          = text "repeat" <+> parens (pretty step)
  pretty (PrRewrite tm)           = text "rewrite" <+> parens (pretty tm)
  pretty (PrRewriter)             = text "rewriter"
  pretty (PrEasy)                 = text "easy"
  pretty (PrTactic s ts)          = text s <+> hsep (map (parens . pretty) ts)
  pretty (PrPoseProof tm)         = text "pose proof" <+> parens (pretty tm)
  pretty (PrPoseProofAs tm id)    = hsep
                                      [ text "pose proof",
                                        parens (pretty tm),
                                        text "as",
                                        pretty id
                                      ]
  pretty (PrBullet lvl steps) = char c <+>
                                    vsep (punctuate (char '.')
                                            (lpretty steps))
    where c                   = case lvl of
                0 -> '-'
                1 -> '+'
                2 -> '*'
                _ -> error "Invalid bullet level"
  pretty (PrDestruct tm) = text "destruct" <+> parens (pretty tm)
  pretty (PrFEqual 0 _)  = pretty PrReflexivity
  pretty (PrFEqual a tm) = pretty (PrApply (TermApp fe [tm]))
    where fe' | a == 1    = "f_equal"
              | otherwise = "f_equal" ++ show a
          fe = TermQualId . Ident $ ID fe'
  pretty (PrReflexivity) = text "reflexivity"
  pretty (PrMatchGoal contextrules) =
    vsep
      [ text "match goal with"
      , indent 2 (vpretty contextrules)
      , text "end"
      ]
  pretty (PrClear ids) = hsep (text "clear":map pretty ids)

instance Pretty ContextRule where
  pretty (ContextRule hyps goal tactic) =
    hsep $ text "|" : punctuate comma (lpretty hyps) ++
          [ text "|-", pretty goal, text "=>", pretty tactic ]

instance Pretty ContextHyp where
  pretty (ContextHyp id pat) =
    hsep [ pretty id, colon , pretty pat ]

instance Pretty ClassDeclaration where
  pretty (ClassDeclaration name params mbSort methods) =
    hsep $ concat
      [ [text "Class", pretty name],
        lpretty params,
        case mbSort of
          Just sort -> [colon,pretty sort]
          Nothing   -> [],
        [text ":=", text "{"],
        punctuate' (char ';') (lpretty methods),
        [text "}"]
      ]

instance Pretty MethodDeclaration where
  pretty (MethodDeclaration field binders tm) =
    hsep $ concat
      [ [pretty field],
        lpretty binders,
        [colon,pretty tm]
      ]

instance Pretty ClassInstance where
  pretty (ClassInstance nm binders cl params methods) =
    fsep [text "Global",
          text "Instance",
          pretty nm,
          hsep (lpretty binders),
          colon,
          hsep (pretty cl : lpretty params),
          text ":="
         ] <$$>
    indent 2 (
      fsep $
        text "{|" :
        punctuate' (char ';') (lpretty methods) ++
        [text "|}"]
    )

instance Pretty Method where
  pretty (Method nm ps tm) =
    fsep $ concat
      [ [pretty nm],
        lpretty ps,
        [text ":=", pretty tm]
      ]
