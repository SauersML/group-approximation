import GroupApproximation.Manuscript.MFRecognition.RopeRecognitionInputs
import GroupApproximation.Manuscript.MFRecognition.MarkedHigmanRopeInput
import GroupApproximation.Manuscript.MFRecognition.BridgeUniformPresentation
import GroupApproximation.Manuscript.MFRecognition.SeedPresentation
import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridgeInjective
import GroupApproximation.Manuscript.MFRecognition.RecognitionMainTheorem
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceDischarge
import GroupApproximation.Manuscript.MFRecognition.EffectiveHigmanCompiler

/-!
# `thm:recognition`: the family `e ↦ R̂_e`, assembled

`RecognitionMainTheorem` proves every clause of `thm:recognition` from a
`RecognitionFamily`: a computable `e ↦ R̂_e` that is not MF on `FIN`
(`lem:negative-branch`) and MF on `INF` (`lem:positive-branch`), and
`recognitionFamily_of_inputs` builds that family from a
`RecognitionInputs e …` for every `e`.  This module builds those inputs from
the landed pieces, in the printed order:

* `lem:seed` and `lem:switch`: `Switch.H`, `Switch.switchCode`, the two branch
  isomorphisms (`SeedPresentation`);
* `lem:bridge`: `Q_e = B(C_e)` on `x, y, t`, coded uniformly
  (`BridgeUniformPresentation`), with `C_e ↪ Q_e`, `j : Q₊ ↪ P`, and
  `Q_e = Q₊` on `INF` (`ThreeGeneratorBridge*`);
* `lem:mikhailova`: a marked Higman output `o e` for the code of `Q_e`, which
  is the one algorithmic input the printed lemma cites (Higman, Mikaelian) —
  `EffectiveHigmanCompiler` supplies one for every `e` at once;
* `lem:central-rope`, `lem:finite-rope`: the rope objects of
  `MarkedHigmanRopeInput`, `RopeObjects`, `FiniteRope`, read through
  `RopeRecognitionInputs`;
* `thm:hnn-permanence`: the analytic bundle, from Shulman's Theorem 16 and
  Ueda's Proposition 2.4 (`HNNPermanenceDischarge`).

What remains open on the effectivity side is the *code* of `R̂_e`: the finite
presentation `eq:finite-rope` as a `PresentationCode` computable from `e`
whose group is `FiniteRope`.  The raw transformation and its semantics are
`Higman.MikhailovaRopeCode.compileRankThree` and
`Higman.MikhailovaRopeCodeSemantics.compileEquivToRope`; wiring them to the
marked outputs is the `RopeCodeFamily` datum below.  With it, and the two
analytic citations, and the marked outputs, every printed clause of
`thm:recognition` follows (`manuscriptRecognition_of`).
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace Assembly

open SecondLevelIndexSets
open Rope Rope.RopeInput
open BridgeUniform

noncomputable section

/-! ## `Q_e = B(C_e)`, coded from the seed switch -/

/-- The manuscript's `Q_e = B(C_e)` on `x, y, t`: the uniform bridge
presentation applied to the recursive presentation of `C_e`. -/
def qcodeSeed (e : Nat.Partrec.Code) : RecPresCode :=
  TS.rankThreeCode (Switch.switchCode e)

theorem computable_qcodeSeed : Computable qcodeSeed :=
  TS.computable_rankThreeCode.comp Switch.switchCode_computable

/-- **`lem:bridge`(2) at `Q_e`**: `N_e ≤ N₊`. -/
theorem kernelN_qcodeSeed_le (e : Nat.Partrec.Code) :
    kernelN (qcodeSeed e) ≤ Bridge.qPlus.ker := by
  rw [qcodeSeed, kernelN_rankThreeCode_eq]
  exact Bridge.NC_le_Nplus _

/-- **`lem:bridge`(2), the equality clause, at `Q_e` for `e ∈ INF`**:
`N_e = N₊` because `C_e` is trivial. -/
theorem kernelN_qcodeSeed_eq_of_infiniteDomain (e : Nat.Partrec.Code)
    (he : InfiniteDomain e) : kernelN (qcodeSeed e) = Bridge.Nplus := by
  haveI := Switch.switchGroup_subsingleton_of_infiniteDomain e he
  rw [qcodeSeed, kernelN_rankThreeCode_eq]
  exact Bridge.manuscriptBridge_two_trivial _

/-! ## The rope input at `e` -/

variable {e : Nat.Partrec.Code}

/-- The concrete rope input of `eq:central-rope` at `e`, from a marked Higman
output for `Q_e` and the bridge map `j`. -/
def ropeInputOf (o : MarkedHigmanOutput (qcodeSeed e)) : RopeInput :=
  o.ropeInput Bridge.qPlus Bridge.jQ Bridge.jQ_injective (kernelN_qcodeSeed_le e)

/-- **`lem:bridge`(1) at `e`**: `C_e` embeds in `Q_e`. -/
theorem embed_C_Q (o : MarkedHigmanOutput (qcodeSeed e)) :
    ∃ f : Switch.SwitchGroup e →* Qe (ropeInputOf o), Function.Injective f :=
  ⟨(presentedRankThreeEquiv (Switch.switchCode e)).symm.toMonoidHom.comp
      (Bridge.embC _),
    (presentedRankThreeEquiv (Switch.switchCode e)).symm.injective.comp
      (Bridge.embC_injective _)⟩

instance instNormalKernelN (e : Nat.Partrec.Code) : (kernelN (qcodeSeed e)).Normal :=
  Subgroup.normalClosure_normal

/-- "if `e ∈ INF` then `Q_e = Q₊`". -/
def qeEquivQplus (o : MarkedHigmanOutput (qcodeSeed e)) (he : InfiniteDomain e) :
    Qe (ropeInputOf o) ≃* Bridge.Qplus :=
  (QuotientGroup.quotientMulEquivOfEq
      (kernelN_qcodeSeed_eq_of_infiniteDomain e he)).trans
    (QuotientGroup.quotientKerEquivOfSurjective Bridge.qPlus
      (Bridge.qC_surjective Bridge.trivSeq Bridge.trivSeq_spans))

/-- "... `N_e = N₊` and `q_e = q₊`". -/
theorem qeEquivQplus_qe (o : MarkedHigmanOutput (qcodeSeed e)) (he : InfiniteDomain e)
    (f : Fxyt) : qeEquivQplus o he (qe (ropeInputOf o) f) = Bridge.qPlus f := by
  show (QuotientGroup.quotientKerEquivOfSurjective Bridge.qPlus
      (Bridge.qC_surjective Bridge.trivSeq Bridge.trivSeq_spans))
    ((QuotientGroup.quotientMulEquivOfEq (kernelN_qcodeSeed_eq_of_infiniteDomain e he))
      (QuotientGroup.mk f)) = Bridge.qPlus f
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

instance : Countable Bridge.Qplus := Bridge.jQ_injective.countable

instance (o : MarkedHigmanOutput (qcodeSeed e)) : Countable (ropeInputOf o).Qplus :=
  Bridge.jQ_injective.countable

/-- **The inputs of the two branch lemmas at `e`.** -/
def recognitionInputsOf (o : MarkedHigmanOutput (qcodeSeed e)) :
    Recognition.RecognitionInputs e Switch.H (Switch.SwitchGroup e) Fxyt Ptarget
      Bridge.Qplus (Qe (ropeInputOf o)) (K0 (ropeInputOf o)) (FiniteRope (ropeInputOf o)) :=
  recognitionInputsOfRope (ropeInputOf o) e Switch.seed_not_isOperatorMF
    (Switch.seed_embeds_switchGroup_of_finiteDomain e) (embed_C_Q o)
    (fun he => ⟨qeEquivQplus o he, qeEquivQplus_qe o he⟩)

/-! ## The family -/

/-- **The code of `eq:finite-rope`.**  A presentation code for `R̂_e`,
computable from `e`, presenting `FiniteRope`.  This is the effectivity clause
of `lem:finite-rope` at the marked outputs; the raw transformation is
`Higman.MikhailovaRopeCode.compileRankThree`, its semantics
`Higman.MikhailovaRopeCodeSemantics.compileEquivToRope`. -/
structure RopeCodeFamily (o : ∀ e, MarkedHigmanOutput (qcodeSeed e)) where
  /-- The code of `R̂_e`. -/
  code : Nat.Partrec.Code → PresentationCodes.PresentationCode
  /-- ... computable from `e`. -/
  computable_code : Computable code
  /-- ... presenting `R̂_e`. -/
  equiv : ∀ e, PresentationCodes.Carrier (code e) ≃* FiniteRope (ropeInputOf (o e))

/-- **`thm:recognition`, the family `e ↦ R̂_e`**, from the HNN permanence
bundle, a marked Higman output for every `Q_e`, and the rope codes. -/
def recognitionFamilyOf (hIn : TensorSynchronization.HNNPermanenceInputs)
    (o : ∀ e, MarkedHigmanOutput (qcodeSeed e)) (R : RopeCodeFamily o) :
    Recognition.RecognitionFamily where
  code := R.code
  computable_code := R.computable_code
  negative := fun e hfin hmf =>
    Recognition.not_isOperatorMF_Rhat (recognitionInputsOf (o e)) hfin
      (hmf.comap (R.equiv e).symm.toMonoidHom (R.equiv e).symm.injective)
  positive := fun e hinf =>
    (Recognition.manuscriptPositiveBranch hIn (recognitionInputsOf (o e)) hinf).2.comap
      (R.equiv e).toMonoidHom (R.equiv e).injective

/-- The marked outputs, from the cited effective Higman compiler
(`lem:mikhailova`, Higman/Mikaelian). -/
def markedOutputsOfCompiler (h : EffectiveHigmanCompiler) :
    ∀ e, MarkedHigmanOutput (qcodeSeed e) :=
  fun e => (h.marks (qcodeSeed e)).choose

/-- **`thm:recognition`, every printed clause**, from Shulman's Theorem 16,
Ueda's Proposition 2.4, the marked outputs of `lem:mikhailova`, and the rope
codes of `lem:finite-rope`. -/
theorem manuscriptRecognition_of
    (hShulman : HNNPermanence.ShulmanTheorem16Statement)
    (hUeda : HNNPermanence.UedaCornerMapStatement)
    (o : ∀ e, MarkedHigmanOutput (qcodeSeed e)) (R : RopeCodeFamily o) :
    ArithmeticalHierarchy.Pi02 MFRecognitionSecondLevel.MFCode ∧
      ArithmeticalHierarchy.Sigma02 MFRecognitionSecondLevel.NonMFCode ∧
      ArithmeticalHierarchy.Pi02Complete MFRecognitionSecondLevel.MFCode ∧
      ArithmeticalHierarchy.Sigma02Complete MFRecognitionSecondLevel.NonMFCode ∧
      ¬ ComputablePred MFRecognitionSecondLevel.MFCode ∧
      (¬ ∃ f : PresentationCodes.PresentationCode → Bool,
        Computable f ∧ ∀ c, f c = true ↔ MFRecognitionSecondLevel.MFCode c) ∧
      ¬ REPred MFRecognitionSecondLevel.MFCode ∧
      ¬ REPred MFRecognitionSecondLevel.NonMFCode ∧
      (∃ f : Nat.Partrec.Code → PresentationCodes.PresentationCode, Computable f ∧
        ∀ e, IsOperatorMF (PresentationCodes.Carrier (f e)) ↔ InfiniteDomain e) :=
  Recognition.manuscriptRecognition
    (recognitionFamilyOf (HNNPermanence.hnnPermanenceInputs_of_citations hShulman hUeda)
      o R)

/-- **`thm:recognition`, the `Π⁰₂`-completeness clause**, from the two analytic
citations, the cited effective Higman compiler, and the rope codes. -/
theorem mfPresentations_pi02Complete_of
    (hShulman : HNNPermanence.ShulmanTheorem16Statement)
    (hUeda : HNNPermanence.UedaCornerMapStatement)
    (h : EffectiveHigmanCompiler) (R : RopeCodeFamily (markedOutputsOfCompiler h)) :
    ArithmeticalHierarchy.Pi02Complete MFRecognitionSecondLevel.MFCode :=
  Recognition.mfPresentations_pi02Complete
    (recognitionFamilyOf (HNNPermanence.hnnPermanenceInputs_of_citations hShulman hUeda)
      (markedOutputsOfCompiler h) R)

end

end Assembly
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
