import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# The sentence that introduces the Clifford witness

`non_mf_groups_exist.tex`, Section `sec:amenable-nonqd`, the paragraph before
`\label{eq:affine-clifford-witness}` (tex 1920–1923 at origin/main 5b3910136):

> We now construct a group to which Theorem~\ref{thm:compression-criterion} applies through a
> finite central subgroup: its intrinsic defect subgroup contains a commutator whose square is a
> central involution.

For every group `Γ`, injective `α : Γ →* Γ` and `a ∉ range α`, the witness is
`W = MarkedCompression.Ambient α hα`, and the Kazhdan subgroup is the level-zero copy
`CliffordWitnessDirectDefect.baseSubgroup α hα` of `Γ`.  The commutator is the pointwise defect
`d = [t c t⁻¹, ι(a)]` (`CliffordWitnessDirectDefect.pointDefect`).  It lies in the intrinsic defect
subgroup `𝔇_W(Γ) = printedDefect (baseSubgroup α hα)`, and its square is the central sign `ε`
(`sign_eq_pointDefect_sq`).  The finite central subgroup through which the criterion applies is
`⟨ε⟩ = signSubgroup α hα`.
-/

namespace GroupApproximation
namespace CliffordDefectCommutatorSentence

open MarkedCompression CliffordWitnessDirectDefect
open scoped commutatorElement

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- **Printed sentence (tex 1920–1923), second clause.**

> its intrinsic defect subgroup contains a commutator whose square is a central involution.

The commutator is `d = [t c t⁻¹, ι(a)]`; `d²` commutes with every element of `W`, is not `1`, and
squares to `1`. -/
theorem manuscriptSentence_defectContainsCommutatorSquaringToCentralInvolution
    {a : Γ} (ha : a ∉ Set.range α) :
    ∃ d ∈ Manuscript.OneSidedMFRadical.printedDefect (baseSubgroup α hα),
      (∃ x y : Ambient α hα, d = ⁅x, y⁆) ∧
        (∀ g : Ambient α hα, Commute (d ^ 2) g) ∧ d ^ 2 ≠ 1 ∧ (d ^ 2) ^ 2 = 1 := by
  refine ⟨pointDefect α hα a, pointDefect_mem_printedDefect α hα a,
    ⟨compressionRoot α hα, iotaAmbient α hα a, rfl⟩, ?_, ?_, ?_⟩
  · intro g
    rw [← sign_eq_pointDefect_sq α hα ha]
    exact signAmbient_central α hα g
  · rw [← sign_eq_pointDefect_sq α hα ha]
    exact signAmbient_ne_one α hα
  · rw [← sign_eq_pointDefect_sq α hα ha]
    exact signAmbient_sq α hα

/-- **Printed sentence (tex 1920–1923), first clause.**

> We now construct a group to which Theorem~\ref{thm:compression-criterion} applies through a
> finite central subgroup

The subgroup `⟨ε⟩` is finite, nontrivial and central, and it lies in the intrinsic defect subgroup
of the level-zero copy of `Γ`. -/
theorem manuscriptSentence_finiteCentralSubgroupInDefect {a : Γ} (ha : a ∉ Set.range α) :
    ∃ K : Subgroup (Ambient α hα), Finite K ∧ Nontrivial K ∧
      (∀ k ∈ K, ∀ g : Ambient α hα, Commute k g) ∧
        K ≤ Manuscript.OneSidedMFRadical.printedDefect (baseSubgroup α hα) := by
  refine ⟨signSubgroup α hα, inferInstance, inferInstance, ?_,
    signSubgroup_le_printedDefect α hα ha⟩
  intro k hk g
  change k = 1 ∨ k = signAmbient α hα at hk
  rcases hk with rfl | rfl
  · exact Commute.one_left g
  · exact signAmbient_central α hα g

end CliffordDefectCommutatorSentence
end GroupApproximation

open GroupApproximation.CliffordDefectCommutatorSentence

#audit_axioms manuscriptSentence_defectContainsCommutatorSquaringToCentralInvolution
#audit_axioms manuscriptSentence_finiteCentralSubgroupInDefect
