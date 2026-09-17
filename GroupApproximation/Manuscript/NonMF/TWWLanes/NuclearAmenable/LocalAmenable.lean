import GroupApproximation.Analysis.AmenableTraceGeneratorDense
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-13, part 1: amenable traces in local form, and the diagonal argument

`QuasidiagonalMF.NuclearAmenableTraceInput` (Analysis/TikuisisWhiteWinterCore.lean:192)
concludes `Quasidiagonal.IsAmenableTrace`, the **sequence** form: one sequence of ucp
matrix models `φₙ`, with Hilbert--Schmidt multiplicative defects and trace defects
tending to zero at **every** pair of elements.  Connes' trick (Brown--Ozawa,
Theorem 6.2.7) produces models only in the **local** form: one model per finite set and
tolerance.  This file supplies that form, `IsLocallyAmenableTrace`, and proves the
passage from local to sequence form on a **separable** algebra.

The route mirrors `Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`
(Analysis/QuasidiagonalTraceLocal.lean:321), with the `2`-norm in place of the operator
norm, and it reuses the dense-generator upgrade
`Quasidiagonal.amenableTraceModel_of_dense_generators`
(Analysis/AmenableTraceGeneratorDense.lean:315).

1. `lipschitz_of_isLocallyAmenableTrace`: the models force `τ` to be `1`-Lipschitz, since
   ucp maps into matrices are contractive (`Quasidiagonal.ucpContractive`, a theorem).
2. Choose a dense sequence `u`.  At stage `n`, take a local model at `{1, u 0, …, u n}`
   with tolerance `1/(n+2)`.  The trace clause at `1` forces the model to be nonempty.
3. On `range u` both defects tend to zero, and the dense-generator upgrade extends them
   to all of `A`.

Everything here is proved.  Nothing is assumed.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearAmenable

open Filter Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **A locally amenable trace.**  For every finite `F ⊆ A` and every `ε > 0` there is a
single unital completely positive map into a matrix algebra whose normalized
Hilbert--Schmidt multiplicative defect on `F × F` and whose trace defect on `F` are at
most `ε`.  It is the `2`-norm analogue of `Quasidiagonal.IsLocallyQuasidiagonalTrace`. -/
def IsLocallyAmenableTrace (τ : A → ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ x ∈ F, ∀ y ∈ F, hsNorm Y (φ (x * y) - φ x * φ y) ≤ ε) ∧
      (∀ x ∈ F, ‖τ x - normTrace Y (φ x)‖ ≤ ε)

/-- **A locally amenable trace is `1`-Lipschitz.**  Only the trace clause at `{x, y}` and
the contractivity of ucp maps are used, exactly as in
`Quasidiagonal.lipschitz_of_isLocallyQuasidiagonalTrace`. -/
theorem lipschitz_of_isLocallyAmenableTrace
    {τ : A → ℂ} (h : IsLocallyAmenableTrace τ) (x y : A) :
    ‖τ x - τ y‖ ≤ ‖x - y‖ := by
  classical
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨Y, φ, hone, hcp, _, htr⟩ := h {x, y} (ε / 2) (by linarith)
  have hx : ‖τ x - normTrace Y (φ x)‖ ≤ ε / 2 :=
    htr x (Finset.mem_insert_self x {y})
  have hy : ‖τ y - normTrace Y (φ y)‖ ≤ ε / 2 :=
    htr y (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  have hmid : ‖normTrace Y (φ x) - normTrace Y (φ y)‖ ≤ ‖x - y‖ := by
    rw [← normTrace_sub, ← map_sub]
    exact (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm Y
      (φ (x - y))).trans
      (ucpContractive.norm_le A inferInstance Y φ hone hcp (x - y))
  have e : τ x - τ y
      = (τ x - normTrace Y (φ x)) + (normTrace Y (φ x) - normTrace Y (φ y))
        - (τ y - normTrace Y (φ y)) := by ring
  rw [e]
  have s1 := norm_sub_le ((τ x - normTrace Y (φ x))
    + (normTrace Y (φ x) - normTrace Y (φ y))) (τ y - normTrace Y (φ y))
  have s2 := norm_add_le (τ x - normTrace Y (φ x))
    (normTrace Y (φ x) - normTrace Y (φ y))
  linarith [s1, s2, hx, hy, hmid]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.lipschitz_of_isLocallyAmenableTrace

/-- **Local ⟹ sequence, on a separable algebra.**  A unital linear functional that is a
locally amenable trace on a separable unital C⋆-algebra is an amenable trace in the
sequence sense of `Quasidiagonal.IsAmenableTrace`.

The hypothesis `τ 1 = 1` is used only to rule out empty models.  Every tracial state
satisfies it. -/
theorem isAmenableTrace_of_isLocallyAmenableTrace
    (hsep : TopologicalSpace.SeparableSpace A) (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1 = 1)
    (h : IsLocallyAmenableTrace ⇑τ) : IsAmenableTrace ⇑τ := by
  classical
  haveI := hsep
  haveI : Nonempty A := ⟨1⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq A
  have hchoice : ∀ n : ℕ, ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧ Nonempty Y ∧
      (∀ i ≤ n, ∀ j ≤ n,
        hsNorm Y (φ (u i * u j) - φ (u i) * φ (u j)) ≤ 1 / ((n : ℝ) + 2)) ∧
      (∀ i ≤ n, ‖τ (u i) - normTrace Y (φ (u i))‖ ≤ 1 / ((n : ℝ) + 2)) := by
    intro n
    obtain ⟨Y, φ, hone, hcp, hmul, htr⟩ :=
      h (insert 1 ((Finset.range (n + 1)).image u)) (1 / ((n : ℝ) + 2)) (by positivity)
    have hmem : ∀ i ≤ n, u i ∈ insert 1 ((Finset.range (n + 1)).image u) := fun i hi ↦
      Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem u (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    have hne : Nonempty Y := by
      by_contra hY
      have hcard : Fintype.card Y = 0 :=
        Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hY)
      have h1 : ‖τ 1 - normTrace Y (φ 1)‖ ≤ 1 / ((n : ℝ) + 2) :=
        htr 1 (Finset.mem_insert_self _ _)
      have hzero : normTrace Y (φ 1) = 0 := by
        unfold normTrace
        rw [hcard, Nat.cast_zero, div_zero]
      rw [hzero, hτ1, sub_zero, norm_one] at h1
      have hlt : 1 / ((n : ℝ) + 2) < 1 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        rw [div_lt_one (by linarith)]
        linarith
      linarith
    exact ⟨Y, φ, hone, hcp, hne, fun i hi j hj ↦ hmul _ (hmem i hi) _ (hmem j hj),
      fun i hi ↦ htr _ (hmem i hi)⟩
  choose Y φ hone hcp hne hmul htr using hchoice
  haveI : ∀ n, Nonempty (Y n) := hne
  have hcontr : ∀ (n : ℕ) (z : A), ‖φ n z‖ ≤ ‖z‖ := fun n z ↦
    ucpContractive.norm_le A inferInstance (Y n) (φ n) (hone n) (hcp n) z
  have hbound : ∀ x : A, ‖τ x‖ ≤ 1 * ‖x‖ := fun x ↦ by
    have hl := lipschitz_of_isLocallyAmenableTrace h x 0
    rw [map_zero, sub_zero, sub_zero] at hl
    rw [one_mul]
    exact hl
  obtain ⟨τc, hτc⟩ : ∃ τc : A →L[ℂ] ℂ, ∀ x, τc x = τ x :=
    ⟨τ.mkContinuous 1 hbound, fun x ↦ LinearMap.mkContinuous_apply τ 1 hbound x⟩
  have hfun : (⇑τc : A → ℂ) = ⇑τ := funext hτc
  have hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 2) < ε := by
    intro ε hε
    filter_upwards [TracialUltraproduct.eventually_lt_of_tendsto_zero
      tendsto_one_div_add_atTop_nhds_zero_nat hε] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact lt_of_le_of_lt (one_div_le_one_div_of_le (by linarith) (by linarith)) hn
  rw [← hfun]
  refine ⟨amenableTraceModel_of_dense_generators φ hone hcp hcontr τc (Set.range u)
    (Dense.mono Submodule.subset_span hu) ?_ ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
      (fun n ↦ hsNorm_nonneg _ _) ?_
    intro ε hε
    filter_upwards [hdiv ε hε, Filter.eventually_ge_atTop i,
      Filter.eventually_ge_atTop j] with n hn hni hnj
    exact (hmul n i hni j hnj).trans_lt hn
  · rintro _ ⟨i, rfl⟩
    refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
      (fun n ↦ norm_nonneg _) ?_
    intro ε hε
    filter_upwards [hdiv ε hε, Filter.eventually_ge_atTop i] with n hn hni
    rw [hτc]
    exact (htr n i hni).trans_lt hn

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.isAmenableTrace_of_isLocallyAmenableTrace

end

end Manuscript.NonMF.TWWLanes.NuclearAmenable
end GroupApproximation
