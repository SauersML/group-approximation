import GroupApproximation.Computability.BenignSupCode
import GroupApproximation.Computability.BenignInfCodeSemantics
import GroupApproximation.Higman.MikhailovaRopeCodeSemantics

/-!
# Semantics of the effective two-HNN benign-join syntax

`BenignSupCode` emits two successive centralizing HNN presentations.  This
file identifies each literal layer with its word-level HNN presentation and
records the images of old words, stable letters, and the conjugate words used
in the final cutter.
-/

namespace GroupApproximation
namespace BenignSupCodeSemantics

open PresentationCodes FreeEdgeTowerCode FreeEdgeTowerSemantics
open BenignSupCode BenignInfCodeSemantics
open Higman.MikhailovaRopeCode
open Higman.MikhailovaRopeCodeSemantics

abbrev Raw : Type := BenignSupCode.Raw

/-- The first computed centralizing layer. -/
noncomputable def level1Equiv (x : BenignSupCode.Input) :
    Carrier (level1 x) ≃*
      HNNPresentation.Ext (codeRels (productBase x))
        (sourceWord (productBase x) (centralEdges (m1Words x)))
        (targetWord (productBase x) (centralEdges (m1Words x)))
        (centralSubgroupEquiv (productBase x) (m1Words x)) :=
  firstStageCodeEquiv (productBase x) (m1Words x)

/-- The second computed centralizing layer. -/
noncomputable def level2Equiv (x : BenignSupCode.Input) :
    Carrier (level2 x) ≃*
      HNNPresentation.Ext (codeRels (level1 x))
        (sourceWord (level1 x) (centralEdges (m2Words x)))
        (targetWord (level1 x) (centralEdges (m2Words x)))
        (centralSubgroupEquiv (level1 x) (m2Words x)) :=
  firstStageCodeEquiv (level1 x) (m2Words x)

theorem firstStageCodeEquiv_oldWord (c : PresentationCode)
    (words : List Raw) (raw : Raw) :
    firstStageCodeEquiv c words
        (evalWord (firstStageCode c words) (DirectProductCode.leftWord c raw)) =
      HNNExtension.of (evalWord c raw) := by
  change edgeCodeEquivOfSubgroupEquiv c (centralEdges words)
      (centralSubgroupEquiv c words) (centralSubgroupEquiv_gen c words)
      (PresentedGroup.mk (codeRels (edgeCode c (centralEdges words)))
        (wordOf (edgeCode c (centralEdges words)) (CoprodCode.normWord c raw))) = _
  exact edgeCodeEquivOfSubgroupEquiv_oldWord c (centralEdges words)
    (centralSubgroupEquiv c words) (centralSubgroupEquiv_gen c words) raw

theorem firstStageCodeEquiv_stable (c : PresentationCode)
    (words : List Raw) :
    firstStageCodeEquiv c words
        (PresentedGroup.of
          (letterOf (firstStageCode c words) (stableIndex c))) =
      (HNNExtension.t :
        HNNPresentation.Ext (codeRels c)
          (sourceWord c (centralEdges words))
          (targetWord c (centralEdges words))
          (centralSubgroupEquiv c words)) := by
  exact edgeCodeEquivOfSubgroupEquiv_stable c (centralEdges words)
    (centralSubgroupEquiv c words) (centralSubgroupEquiv_gen c words)

/-- The raw conjugate emitted by `firstStableConjugate` has its literal HNN
meaning under the concrete first-stage equivalence. -/
theorem firstStageCodeEquiv_conjugate (c : PresentationCode)
    (words : List Raw) (raw : Raw) :
    firstStageCodeEquiv c words
        (evalWord (firstStageCode c words) (firstStableConjugate c raw)) =
      (HNNExtension.t :
          HNNPresentation.Ext (codeRels c)
            (sourceWord c (centralEdges words))
            (targetWord c (centralEdges words))
            (centralSubgroupEquiv c words))⁻¹ *
        HNNExtension.of (evalWord c raw) * HNNExtension.t := by
  have hs := firstStageCodeEquiv_stable c words
  change firstStageCodeEquiv c words
      (PresentedGroup.mk (codeRels (firstStageCode c words))
        (FreeGroup.of (letterOf (firstStageCode c words) (stableIndex c)))) =
    HNNExtension.t at hs
  have hw := firstStageCodeEquiv_oldWord c words raw
  change firstStageCodeEquiv c words
      (PresentedGroup.mk (codeRels (firstStageCode c words))
        (wordOf (firstStageCode c words) (DirectProductCode.leftWord c raw))) =
    HNNExtension.of (evalWord c raw) at hw
  simp only [firstStableConjugate, RawWord.wordOf_cons_neg,
    RawWord.wordOf_append, RawWord.wordOf_cons_pos, RawWord.wordOf_nil,
    mul_one, map_mul, map_inv, evalWord]
  rw [hs, hw]
  rfl

/-- First-level conjugate words, before insertion into the second layer. -/
theorem level1Equiv_firstConjugate (x : BenignSupCode.Input) (raw : Raw) :
    level1Equiv x
        (evalWord (level1 x) (firstStableConjugate (productBase x) raw)) =
      (HNNExtension.t :
          HNNPresentation.Ext (codeRels (productBase x))
            (sourceWord (productBase x) (centralEdges (m1Words x)))
            (targetWord (productBase x) (centralEdges (m1Words x)))
            (centralSubgroupEquiv (productBase x) (m1Words x)))⁻¹ *
        HNNExtension.of (evalWord (productBase x) raw) * HNNExtension.t :=
  firstStageCodeEquiv_conjugate (productBase x) (m1Words x) raw

/-- Second-level conjugate words have the analogous literal meaning. -/
theorem level2Equiv_secondConjugate (x : BenignSupCode.Input) (raw : Raw) :
    level2Equiv x
        (evalWord (level2 x) (firstStableConjugate (level1 x) raw)) =
      (HNNExtension.t :
          HNNPresentation.Ext (codeRels (level1 x))
            (sourceWord (level1 x) (centralEdges (m2Words x)))
            (targetWord (level1 x) (centralEdges (m2Words x)))
            (centralSubgroupEquiv (level1 x) (m2Words x)))⁻¹ *
        HNNExtension.of (evalWord (level1 x) raw) * HNNExtension.t :=
  firstStageCodeEquiv_conjugate (level1 x) (m2Words x) raw

end BenignSupCodeSemantics
end GroupApproximation
