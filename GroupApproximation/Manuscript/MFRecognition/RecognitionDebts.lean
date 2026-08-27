import GroupApproximation.Manuscript.MFRecognition.RecognitionAssembly
import GroupApproximation.Higman.CurrentREBenign

/-!
# `thm:recognition`, closed: the remaining inputs as recorded debts

`RecognitionAssembly.manuscriptRecognition_of` proves every printed clause of
`thm:recognition` from four inputs.  This module records each of them as a
declaration whose proof is `sorry`, so that the debt is visible in the
kernel's axiom report instead of a leading binder, and closes the theorem on
top of them:

* `shulmanTheorem16` — Shulman, Theorem 16 (amalgamated free products of
  separable `C*`-algebras are MF under compatible corona embeddings);
* `uedaCornerMap` — Ueda, Proposition 2.4 (the universal `C*`-HNN algebra is
  a full corner of the amalgam), blocked in-repo by the universe gap recorded
  on `UedaCornerMapStatement`;
* `omegaInput` — Higman's ω-closure, the one construction the benign-subgroup
  route to Higman's embedding theorem still owes; with it Higman's theorem is
  the theorem `reBenign` below;
* `effectiveHigmanCompiler` — the effective, marked form of Higman's theorem
  (Mikaelian's algorithm) on the rank-three family;
* `ropeCodeFamily` — the code of `eq:finite-rope`, computable from `e` and
  presenting `R̂_e`, from `Higman.MikhailovaRopeCode.compileRankThree` and
  `Higman.MikhailovaRopeCodeSemantics.compileEquivToRope`.

The printed nonunital form of `thm:hnn-permanence` is recorded the same way:
its passage from the unital form is the corner compression `p𝒬p ≅ 𝒬'`.
-/

set_option warningAsError false

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HigmanCompiler
namespace Assembly

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-! ## The analytic debts -/

/-- **DEBT (literature).**  Shulman, Theorem 16. -/
theorem shulmanTheorem16 : HNNPermanence.ShulmanTheorem16Statement := by
  sorry

/-- **DEBT (literature).**  Ueda, Proposition 2.4, as the corner map. -/
theorem uedaCornerMap : HNNPermanence.UedaCornerMapStatement := by
  sorry

/-- **`thm:hnn-permanence`, printed form, with a possibly nonunital `ι`.**
Printed: *"an injective `*`-homomorphism `ι : A → 𝒬` and a unitary `W ∈ 𝒬`
with `W ιρ(s) W* = ιρ(θ(s))`."*  **DEBT (proof):** the passage from the
unital form is the compression of `𝒬` to the corner `p𝒬p`, `p = ι(1)`, which
is again a norm matrix corona. -/
theorem manuscriptHNNPermanence_nonunital
    {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsRegularlyRealized (HNNExtension G S T phi) := by
  sorry

/-! ## Higman's embedding theorem -/

/-- **DEBT (construction).**  Higman's ω-closure: the three-stage tower proving
that `ω_m` preserves benignness. -/
theorem omegaInput_nonempty : Nonempty Higman.Omega.OmegaInput := by
  sorry

/-- The ω-closure, as a term. -/
def omegaInput : Higman.Omega.OmegaInput := omegaInput_nonempty.some

/-- **Higman's embedding theorem** (recursively enumerable normal subgroups of
finitely generated free groups are benign), closed on the ω-debt. -/
theorem reBenign : Higman.REBenign := Higman.reBenign_of_omega omegaInput

/-- **DEBT (construction).**  The effective marked form of Higman's theorem
(Mikaelian's algorithm): a computable compiler from recursive presentations on
three generators to finite presentations with marked embedding words. -/
theorem effectiveHigmanCompiler_nonempty : Nonempty EffectiveHigmanCompiler := by
  sorry

/-- The compiler, as a term. -/
def effectiveHigmanCompiler : EffectiveHigmanCompiler :=
  effectiveHigmanCompiler_nonempty.some

/-- The marked outputs of `lem:mikhailova` at every `Q_e`. -/
def markedOutputs : ∀ e, MarkedHigmanOutput (qcodeSeed e) :=
  markedOutputsOfCompiler effectiveHigmanCompiler

/-! ## The finite-rope codes -/

/-- **DEBT (effectivity).**  The code of `eq:finite-rope`, computable from
`e`, presenting `R̂_e`. -/
theorem ropeCodeFamily_nonempty : Nonempty (RopeCodeFamily markedOutputs) := by
  sorry

/-- The rope codes, as a term. -/
def ropeCodeFamily : RopeCodeFamily markedOutputs := ropeCodeFamily_nonempty.some

/-! ## `thm:recognition`, closed -/

/-- **The family `e ↦ R̂_e` of `thm:recognition`**, as a closed term. -/
def recognitionFamily : Recognition.RecognitionFamily :=
  recognitionFamilyOf
    (HNNPermanence.hnnPermanenceInputs_of_citations shulmanTheorem16 uedaCornerMap)
    markedOutputs ropeCodeFamily

/-- **`thm:recognition`, the `Π⁰₂`-completeness clause**, closed on the
recorded debts. -/
theorem mfPresentations_pi02Complete :
    ArithmeticalHierarchy.Pi02Complete MFRecognitionSecondLevel.MFCode :=
  Recognition.mfPresentations_pi02Complete recognitionFamily

/-- **`thm:recognition`, the `Σ⁰₂`-completeness clause**, closed on the
recorded debts. -/
theorem nonMFPresentations_sigma02Complete :
    ArithmeticalHierarchy.Sigma02Complete MFRecognitionSecondLevel.NonMFCode :=
  Recognition.nonMFPresentations_sigma02Complete recognitionFamily

/-- **`thm:recognition`, every printed clause**, closed on the recorded
debts. -/
theorem manuscriptRecognition :
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
        ∀ e, IsOperatorMF (PresentationCodes.Carrier (f e)) ↔
          SecondLevelIndexSets.InfiniteDomain e) :=
  Recognition.manuscriptRecognition recognitionFamily

end

end Assembly
end HigmanCompiler
end MFRecognition
end Manuscript
end GroupApproximation
