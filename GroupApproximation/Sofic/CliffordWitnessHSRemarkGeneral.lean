import GroupApproximation.Sofic.CliffordWitnessHSRemark
import GroupApproximation.Sofic.CliffordWitnessSoficPrinted
import GroupApproximation.Meta.AxiomGuard

/-!
# Where operator norm enters, for every Clifford witness `W`

The remark after Proposition `prop:clifford-locally-rf` in `non_mf_groups_exist.tex`
(Section `sec:amenable-nonqd`, tex 2062–2068) is about the group
`W = Cl(X) ⋊ V` of that proposition:

> Soficity also shows where operator norm enters.  The permutation matrices `V_n`
> of a sofic approximation of `W` satisfy `‖V_n(gh) - V_n(g)V_n(h)‖₂ → 0`, while
> `‖V_n(ε) - 1‖₂ → √2`, because `ε ≠ 1` moves almost every point.  So the collapse
> of Corollary `cor:defect-hs` fails for asymptotic representations in normalized
> Hilbert--Schmidt norm, although `ε` is a central involution of `W` inside
> `𝔇_W(Γ)`.

`CliffordWitnessHSRemark` carries these sentences at the concrete affine instance
`Γ̄ = ℤ³ ⋊ SL₃(ℤ)`.  This module carries them at the printed generality: every
countable residually finite Kazhdan group `Γ`, every injective `α : Γ →* Γ` whose
range has finite index, and every `a ∉ α(Γ)`, with `W = Ambient α hα`.

The models are general (`CliffordWitnessHSRemark.tendsto_hsNorm_modelUnitary_mul`,
`tendsto_hsNorm_modelUnitary_sub_one`, `tendsto_movedFraction_of_ne_one`), and `W`
is sofic by `AmenableTraceTheorem.isSofic_ambient_of_residuallyFinite`, the
soficity clause of `prop:clifford-locally-rf`.
-/

namespace GroupApproximation
namespace CliffordWitnessHSRemarkGeneral

open Filter SoficPermutationTrace MarkedCompression CliffordWitnessDirectDefect
open CliffordWitnessHSRemark Manuscript.OneSidedMFRadical
open scoped Topology

/-- **Printed sentence** (tex 2063–2066), at the printed generality.

> The permutation matrices `V_n` of a sofic approximation of `W` satisfy
> `‖V_n(gh) - V_n(g)V_n(h)‖₂ → 0`, while `‖V_n(ε) - 1‖₂ → √2`, because `ε ≠ 1`
> moves almost every point.

For every Clifford witness `W` of `prop:clifford-locally-rf`, a sofic approximation
exists, and along every one the models `V_n(g) = permMatrix (σ_n(g)⁻¹)` are
asymptotically multiplicative in normalized Hilbert--Schmidt norm, `σ_n(ε)` moves
almost every point, and `‖V_n(ε) - 1‖₂ → √2`. -/
def PrintedCliffordWitnessSoficModelsHS : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] [Group.ResiduallyFinite Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex]
    (a : Γ) (_ : a ∉ Set.range α) (_ : HasKazhdanPropertyT.{0, 0} Γ),
    Nonempty (SoficApproximation (Ambient α hα)) ∧
      ∀ S : SoficApproximation (Ambient α hα),
        (∀ g h : Ambient α hα, Tendsto (fun n ↦ hsNorm (S.model n)
          (modelUnitary S n (g * h) - modelUnitary S n g * modelUnitary S n h))
            atTop (𝓝 0)) ∧
        Tendsto (fun n ↦
            ((S.map n (signAmbient α hα)).support.card : ℝ) / Fintype.card (S.model n))
          atTop (𝓝 1) ∧
        Tendsto (fun n ↦ hsNorm (S.model n) (modelUnitary S n (signAmbient α hα) - 1))
          atTop (𝓝 (Real.sqrt 2))

theorem manuscriptCliffordWitnessSoficModelsHS : PrintedCliffordWitnessSoficModelsHS := by
  intro Γ _ _ _ α hα _ _ _ _
  refine ⟨?_, fun S ↦ ⟨fun g h ↦ tendsto_hsNorm_modelUnitary_mul S g h,
    tendsto_movedFraction_of_ne_one S (signAmbient_ne_one α hα),
    tendsto_hsNorm_modelUnitary_sub_one S (signAmbient_ne_one α hα)⟩⟩
  obtain ⟨S, -⟩ := SoficEnvelopeExistence.exists_positive_soficApproximation
    (AmenableTraceTheorem.isSofic_ambient_of_residuallyFinite α hα)
  exact ⟨S⟩

/-- **Printed sentence** (tex 2066–2068), at the printed generality.

> So the collapse of Corollary `cor:defect-hs` fails for asymptotic representations
> in normalized Hilbert--Schmidt norm, although `ε` is a central involution of `W`
> inside `𝔇_W(Γ)`.

For every Clifford witness `W` of `prop:clifford-locally-rf` there is a sequence of
unitary models of `W`, asymptotically multiplicative in normalized Hilbert--Schmidt
norm, that does not send `ε` to `1` in that norm, while `ε` is central, an
involution, nontrivial, and in the printed intrinsic defect of the level-zero copy
of `Γ`. -/
def PrintedCliffordWitnessHSCollapseFails : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] [Group.ResiduallyFinite Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex]
    (a : Γ) (_ : a ∉ Set.range α) (_ : HasKazhdanPropertyT.{0, 0} Γ),
    (∃ (d : ℕ → FiniteModel) (V : (n : ℕ) → Ambient α hα → Matrix (d n) (d n) ℂ),
        (∀ n g, V n g ∈ Matrix.unitaryGroup (d n) ℂ) ∧
        (∀ g h : Ambient α hα,
          Tendsto (fun n ↦ hsNorm (d n) (V n (g * h) - V n g * V n h)) atTop (𝓝 0)) ∧
        ¬ Tendsto (fun n ↦ hsNorm (d n) (V n (signAmbient α hα) - 1)) atTop (𝓝 0)) ∧
      (∀ w : Ambient α hα, Commute (signAmbient α hα) w) ∧
      signAmbient α hα ^ 2 = 1 ∧
      signAmbient α hα ≠ 1 ∧
      signAmbient α hα ∈ printedDefect (baseSubgroup α hα)

theorem manuscriptCliffordWitnessHSCollapseFails : PrintedCliffordWitnessHSCollapseFails := by
  intro Γ _ _ _ α hα _ a ha hT
  obtain ⟨⟨S⟩, hS⟩ := manuscriptCliffordWitnessSoficModelsHS Γ α hα a ha hT
  obtain ⟨hmul, -, hsign⟩ := hS S
  refine ⟨⟨S.model, fun n g ↦ modelUnitary S n g,
      fun n g ↦ modelUnitary_mem_unitaryGroup S n g, hmul, fun h0 ↦ ?_⟩,
    signAmbient_central α hα, signAmbient_sq α hα, signAmbient_ne_one α hα, ?_⟩
  · have heq := tendsto_nhds_unique hsign h0
    exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' heq
  · exact signSubgroup_le_printedDefect α hα ha
      ((mem_centralInvolutionSubgroup_iff _ _ _).mpr (Or.inr rfl))

end CliffordWitnessHSRemarkGeneral
end GroupApproximation

#audit_closed_axioms
  GroupApproximation.CliffordWitnessHSRemarkGeneral.manuscriptCliffordWitnessSoficModelsHS

#audit_closed_axioms
  GroupApproximation.CliffordWitnessHSRemarkGeneral.manuscriptCliffordWitnessHSCollapseFails
