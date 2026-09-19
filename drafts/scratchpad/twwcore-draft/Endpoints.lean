import GroupApproximation.Analysis.LanceNuclearAmenable
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCore.QuasidiagonalTraceModels
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCore.RelatedWorkStatements
-- TODO(imports once WO lanes land): Full.TWWKK.<module with kasparovKK>,
-- Full.TWWUCT.<module with satisfiesUCT_reducedObject_of_isAmenable>,
-- Full.TWWSchafhauser.Assembly (isQuasidiagonalTrace_of_satisfiesUCT)

/-!
# Tikuisis--White--Winter endpoints at Kasparov's KK

Lane TWWCore (WO-NN03c-2 and WO-NM16-2).

* `isModelled_top_of_isAmenable`: the TWW step of `thm:fixed-radical-membership`
  (`non_mf_group_notes.tex` l.1376--1378).
* `kasparovKK`, `tikuisisWhiteWinter`: `non_mf_groups_exist.tex` L279--281.
* `blackadarKirchbergAnswer_uctFaithfulTrace`,
  `uctFaithfulTrace_stablyFinite_and_quasidiagonal`: L315--318.
-/

namespace GroupApproximation.Full.TWWCore

/-- **Amenable ⇒ regular-character models on `⊤`** (`thm:fixed-radical-membership`,
`non_mf_group_notes.tex` l.1376--1378).  The steps are:
nuclearity (Lance), the UCT (Tu), and TWW (via Schafhauser), which give a
quasidiagonal canonical trace, followed by `isModelled_top_of_isQuasidiagonalTrace`. -/
theorem isModelled_top_of_isAmenable {G : Type} [Group G] [Countable G]
    (h : GroupApproximation.Amenability.IsAmenable G) :
    GroupApproximation.Full.TWW.IsModelled (⊤ : Subgroup G) :=
  isModelled_top_of_isQuasidiagonalTrace
    (Full.TWWSchafhauser.isQuasidiagonalTrace_of_satisfiesUCT
      (QuasidiagonalMF.reducedObject G)
      (CStarExactness.isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable h)
      (Full.TWWUCT.satisfiesUCT_reducedObject_of_isAmenable h)
      (ReducedGroupCStarTrace.canonicalFaithfulTracialState G))

/-- Kasparov's `KK`-theory. -/
noncomputable def kasparovKK : KK.KasparovTheory.{0} := Full.TWWKK.kasparovKK

/-- **Tikuisis--White--Winter** at Kasparov's `KK` (`non_mf_groups_exist.tex`
L279--281). -/
theorem tikuisisWhiteWinter : TikuisisWhiteWinterStatement kasparovKK :=
  Full.TWWSchafhauser.isQuasidiagonalTrace_of_satisfiesUCT

/-- **The answer on the UCT faithful-trace class** (`non_mf_groups_exist.tex`
L315--318). -/
theorem blackadarKirchbergAnswer_uctFaithfulTrace :
    BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace kasparovKK := by
  intro S hnuc _ huct hτ
  obtain ⟨τ⟩ := hτ
  exact isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace S.separable τ
    (tikuisisWhiteWinter S hnuc huct τ)

/-- Every separable nuclear UCT algebra with a faithful tracial state is stably
finite and quasidiagonal (`non_mf_groups_exist.tex` L315--318). -/
theorem uctFaithfulTrace_stablyFinite_and_quasidiagonal (S : KK.SepCStarAlgebra.{0})
    (hnuc : CStarExactness.IsNuclearCStarAlgebra S) (huct : kasparovKK.SatisfiesUCT S)
    (τ : FaithfulTracialState S) :
    IsStablyFiniteCStarAlgebra S ∧ IsQuasidiagonalCStarAlgebra S :=
  ⟨stablyFinite_of_mem_answerClass S ⟨τ⟩,
    blackadarKirchbergAnswer_uctFaithfulTrace S hnuc
      (stablyFinite_of_mem_answerClass S ⟨τ⟩) huct ⟨τ⟩⟩

end GroupApproximation.Full.TWWCore
