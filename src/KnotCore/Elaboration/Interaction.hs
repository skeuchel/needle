
module KnotCore.Elaboration.Interaction where

import qualified Coq.Syntax as Coq

import KnotCore.Elaboration.Hints
import KnotCore.Elaboration.Identifiers
import KnotCore.Elaboration.Monad
import KnotCore.Syntax

import KnotCore.Elaboration.Interaction.ShiftComm as ShiftComm
import KnotCore.Elaboration.Interaction.ShiftCommInd as ShiftCommInd
import KnotCore.Elaboration.Interaction.ShiftIndexCommInd as ShiftIndexCommInd
import KnotCore.Elaboration.Interaction.ShiftSubstComm as ShiftSubstComm
import KnotCore.Elaboration.Interaction.ShiftSubstCommInd as ShiftSubstCommInd
import KnotCore.Elaboration.Interaction.ShiftSubstIndexCommInd as ShiftSubstIndexCommInd
import KnotCore.Elaboration.Interaction.SubstIndexShiftIndexReflectionInd as SubstIndexShiftIndexReflectionInd
import KnotCore.Elaboration.Interaction.SubstShiftComm as SubstShiftComm
import KnotCore.Elaboration.Interaction.SubstShiftCommInd as SubstShiftCommInd
import KnotCore.Elaboration.Interaction.SubstShiftIndexCommInd as SubstShiftIndexCommInd
import KnotCore.Elaboration.Interaction.SubstShiftReflection as SubstShiftReflection
import KnotCore.Elaboration.Interaction.SubstShiftReflectionInd as SubstShiftReflectionInd
import KnotCore.Elaboration.Interaction.SubstSubord as SubstSubord
import KnotCore.Elaboration.Interaction.SubstSubordInd as SubstSubordInd
import KnotCore.Elaboration.Interaction.SubstSubstComm as SubstSubstComm
import KnotCore.Elaboration.Interaction.SubstSubstCommInd as SubstSubstCommInd
import KnotCore.Elaboration.Interaction.SubstSubstIndexCommInd as SubstSubstIndexCommInd
import KnotCore.Elaboration.Interaction.SubstSubstIndexCommLeftInd as SubstSubstIndexCommLeftInd
import KnotCore.Elaboration.Interaction.WeakenShift as WeakenShift
import KnotCore.Elaboration.Interaction.WeakenSubst as WeakenSubst

lemmas :: Elab m => [NamespaceDecl] -> [SortGroupDecl] -> m [Coq.Sentence]
lemmas nds sgds = do
  shiftIndexCommInd           <- ShiftIndexCommInd.lemmas nds
  shiftCommInd                <- ShiftCommInd.lemmas sgds
  shiftComm                   <- ShiftComm.lemmas sgds
  substIndexShiftIndexInd     <- SubstIndexShiftIndexReflectionInd.lemmas nds
  substShiftReflectionInd     <- SubstShiftReflectionInd.lemmas sgds
  substShiftReflection        <- SubstShiftReflection.lemmas sgds
  shiftSubstIndexCommInd      <- ShiftSubstIndexCommInd.lemmas nds
  shiftSubstCommInd           <- ShiftSubstCommInd.lemmas sgds
  shiftSubstComm              <- ShiftSubstComm.lemmas sgds
  substShiftIndexCommInd      <- SubstShiftIndexCommInd.lemmas nds
  substShiftCommInd           <- SubstShiftCommInd.lemmas sgds
  substSubordInd              <- SubstSubordInd.lemmas sgds
  substShiftComm              <- SubstShiftComm.lemmas sgds
  substSubord                 <- SubstSubord.lemmas sgds
  substSubstIndexCommRightInd <- SubstSubstIndexCommInd.lemmas nds
  substSubstIndexCommLeftInd  <- SubstSubstIndexCommLeftInd.lemmas nds
  substSubstCommInd           <- SubstSubstCommInd.lemmas sgds
  substSubstComm              <- SubstSubstComm.lemmas sgds

  weakenShift                 <- WeakenShift.lemmas sgds
  weakenSubst                 <- WeakenSubst.lemmas sgds

  substShiftReflectionHints   <- setLemmaSubstShiftReflection >>= mkRewriteHints ["interaction", "reflection"]
  shiftCommHints              <- setLemmaShiftComm            >>= mkRewriteHints ["interaction", "shift_shift0" ]
  substShiftCommHints         <- setLemmaSubstShiftComm       >>= mkRewriteHints ["interaction", "subst_shift0" ]
  substSubordHints            <- setLemmaSubstSubord          >>= mkRewriteHints ["interaction", "subst_shift0" ]
  shiftSubstCommHints         <- setLemmaShiftSubstComm       >>= mkRewriteHints ["interaction", "shift_subst0" ]
  substSubstCommHints         <- setLemmaSubstSubstComm       >>= mkRewriteHints ["interaction", "subst_subst0" ]
  weakenShiftHints            <- setLemmaWeakenShift          >>= mkRewriteHints ["weaken_shift" ]
  weakenSubstHints            <- setLemmaWeakenSubst          >>= mkRewriteHints ["weaken_subst" ]

  let section = Coq.SentenceSection

  -- Interaction
  pure $ concat
    [ [ section (Coq.ID "SubstShiftReflection") $ concat
        [ substIndexShiftIndexInd
        , substShiftReflectionInd
        , substShiftReflection
        ]
      , section (Coq.ID "ShiftInteraction")
        [ section (Coq.ID "ShiftIndexCommInd") shiftIndexCommInd
        , section (Coq.ID "ShiftCommInd") shiftCommInd
        , section (Coq.ID "ShiftComm") shiftComm
        ]
      ]
    , shiftCommHints
    , [ section (Coq.ID "WeakenShift") weakenShift
      , section (Coq.ID "ShiftSubstInteraction")
        [ section (Coq.ID "ShiftSubstIndexCommInd") shiftSubstIndexCommInd
        , section (Coq.ID "ShiftSubstCommInd") shiftSubstCommInd
        , section (Coq.ID "ShiftSubstComm") shiftSubstComm
        , section (Coq.ID "SubstShiftIndexCommInd") substShiftIndexCommInd
        , section (Coq.ID "SubstShiftCommInd") substShiftCommInd
        , section (Coq.ID "SubstShiftComm") substShiftComm
        , section (Coq.ID "SubstSubordInd") substSubordInd
        , section (Coq.ID "SubstSubord") substSubord
        ]
      ]
    , substShiftReflectionHints
    , substShiftCommHints
    , substSubordHints
    , shiftSubstCommHints
    , [ section (Coq.ID "SubstSubstInteraction")
        [ section (Coq.ID "SubstSubstIndexCommInd") $
            substSubstIndexCommRightInd ++ substSubstIndexCommLeftInd
        , section (Coq.ID "SubstSubstCommInd") substSubstCommInd
        , section (Coq.ID "SubstSubstComm") substSubstComm
        , section (Coq.ID "WeakenSubst") weakenSubst
        ]
      ]
    , substSubstCommHints
    , weakenShiftHints
    , weakenSubstHints
    ]
