import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Meta.AxiomGuard

/-!
# Introduction: a compressor conjugates a centralizing element (tex 160–164)

`non_mf_groups_exist.tex`, Introduction (lines 160–164):

> Call `u ∈ G` a *compressor* of `L ≤ G` when `uLu⁻¹ ≤ L`.  An element `c` of the
> centralizer `C_G(L)` commutes with `L`, so `ucu⁻¹` commutes with `uLu⁻¹` but need not
> commute with the rest of `L`.

The second sentence has three clauses.

* `c ∈ C_G(L)` commutes with every element of `L`.
* Hence `ucu⁻¹` commutes with every element `ulu⁻¹` of `uLu⁻¹`, for every group, subgroup
  and element `u`: conjugate the commutation relation.
* "But need not commute with the rest of `L`": some group has a subgroup `L`, a compressor
  `u` of `L` and `c ∈ C_G(L)` with `ucu⁻¹` not commuting with some element of `L`.  The
  witness is the rank-twelve configuration of `prop:defect` in `H = EL₁₂(L_{𝔽₂}(1,2))`.
  There `τ` compresses the upper-left `EL₃` corner and `c` centralizes it, while
  `⁅τcτ⁻¹, ℓ⁆` is the nontrivial defect.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace IntroCompressorCentralizerSentence

/-- **Printed (tex 162–163), the general clauses.**  An element of the centralizer of `L`
commutes with `L`, so its conjugate by any `u` commutes with every conjugate `ulu⁻¹`,
`l ∈ L`. -/
def PrintedCentralizerConjugateCommutes : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G) (u c : G),
    c ∈ Subgroup.centralizer (L : Set G) →
      (∀ l ∈ L, Commute c l) ∧ ∀ l ∈ L, Commute (u * c * u⁻¹) (u * l * u⁻¹)

theorem centralizerConjugateCommutes : PrintedCentralizerConjugateCommutes := by
  intro G _ L u c hc
  have hcomm : ∀ l ∈ L, Commute c l := fun l hl ↦
    show c * l = l * c from ((Subgroup.mem_centralizer_iff.mp hc) l hl).symm
  refine ⟨hcomm, fun l hl ↦ ?_⟩
  have h : c * l = l * c := hcomm l hl
  show u * c * u⁻¹ * (u * l * u⁻¹) = u * l * u⁻¹ * (u * c * u⁻¹)
  calc u * c * u⁻¹ * (u * l * u⁻¹) = u * (c * l) * u⁻¹ := by group
    _ = u * (l * c) * u⁻¹ := by rw [h]
    _ = u * l * u⁻¹ * (u * c * u⁻¹) := by group

/-- **Printed (tex 163–164), "but need not commute with the rest of `L`".**  Some group has
a subgroup `L`, a compressor `u` of `L` and an element `c` of the centralizer of `L` such
that `ucu⁻¹` does not commute with some element of `L`. -/
def PrintedConjugateNeedNotCommute : Prop :=
  ∃ (G : Type) (_ : Group G) (L : Subgroup G) (u c : G),
    (∀ l ∈ L, u * l * u⁻¹ ∈ L) ∧ c ∈ Subgroup.centralizer (L : Set G) ∧
      ∃ l ∈ L, ¬ Commute (u * c * u⁻¹) l

/-- The witness is the rank-twelve configuration: `τ` compresses the corner, `c`
centralizes it, and `⁅τcτ⁻¹, ℓ⁆` is the defect, which is not `1`. -/
theorem conjugateNeedNotCommute : PrintedConjugateNeedNotCommute := by
  refine ⟨OneSidedMFRadical.RankTwelveEndpoint.H, inferInstance,
    OneSidedMFRadical.RankTwelveEndpoint.corner, OneSidedMFRadical.RankTwelveEndpoint.tau,
    OneSidedMFRadical.RankTwelveEndpoint.c,
    OneSidedMFRadical.RankTwelveEndpoint.tau_compresses_corner, ?_,
    OneSidedMFRadical.RankTwelveEndpoint.ell,
    OneSidedMFRadical.RankTwelveEndpoint.ell_mem_corner, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun h hh ↦
      (OneSidedMFRadical.RankTwelveEndpoint.c_commutes_corner h hh).eq.symm
  · intro hcomm
    apply OneSidedMFRadical.RankTwelveEndpoint.defect_ne_one
    rw [← OneSidedMFRadical.RankTwelveEndpoint.tau_c_commutator_ell, commutatorElement_def,
      hcomm.eq]
    group

/-- **Printed (tex 162–164), the whole sentence.** -/
def PrintedCompressorCentralizerSentence : Prop :=
  PrintedCentralizerConjugateCommutes ∧ PrintedConjugateNeedNotCommute

theorem manuscriptSentence_compressorCentralizer : PrintedCompressorCentralizerSentence :=
  ⟨centralizerConjugateCommutes, conjugateNeedNotCommute⟩

end IntroCompressorCentralizerSentence
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.IntroCompressorCentralizerSentence.centralizerConjugateCommutes
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.IntroCompressorCentralizerSentence.conjugateNeedNotCommute
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.IntroCompressorCentralizerSentence.manuscriptSentence_compressorCentralizer
