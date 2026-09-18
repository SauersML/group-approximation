import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDiagonalMatrix

/-!
# Connes' trick: diagonalising the approximately invariant density

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick).
Adapted from the never-wired foreign `TWWLanes/ConnesTrick` module of the same content.

`HasApproxInvariantDensities τ` supplies a ucp model `φ` and a Hermitian `T`
with `tr(T²) = 1`, all clauses stated through traces. Diagonalise `T = U D Uᴴ` with
`D = diag(μ)` and replace `φ` by the compression `B = Uᴴ φ(·) U`. `B` is again ucp
(`ucp_conjLinear_comp`), and every clause turns into an explicit sum over matrix
entries:

* `∑ᵢ μᵢ² = 1`;
* `tr(T φ(x) T) = ∑ᵢ μᵢ² B(x)ᵢᵢ`;
* `‖[φ(x), T]‖₂² = ∑ᵢⱼ |B(x)ᵢⱼ|² (μⱼ - μᵢ)²`;
* `‖(φ(xy) - φ(x)φ(y)) T‖₂² = ∑ᵢⱼ |(B(xy) - B(x)B(y))ᵢⱼ|² μⱼ²`.

The resulting predicate is `HasDiagonalDensities`. The implication
`hasDiagonalDensities_of_hasApproxInvariantDensities` is proved, with no assumptions.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **Diagonal approximately invariant densities.** This is
`HasApproxInvariantDensities` after the density has been diagonalised. Here
`μ` is the list of eigenvalues of `T`, and `B` is the model in the eigenbasis. -/
def HasDiagonalDensities (τ : A → ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (B : A →ₗ[ℂ] Matrix Y Y ℂ) (μ : Y → ℝ),
      B 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑B ∧ ∑ i, μ i ^ 2 = 1 ∧
      (∀ x ∈ F, ‖τ x - ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * B x i i‖ ≤ ε) ∧
      (∀ x ∈ F, ∑ i, ∑ j, Complex.normSq (B x i j) * (μ j - μ i) ^ 2 ≤ ε) ∧
      (∀ x ∈ F, ∀ y ∈ F,
        ∑ i, ∑ j, Complex.normSq ((B (x * y) - B x * B y) i j) * μ j ^ 2 ≤ ε)

/-- **Diagonalisation.** Approximately invariant densities give diagonal ones with the same
tolerance. -/
theorem hasDiagonalDensities_of_hasApproxInvariantDensities {τ : A → ℂ}
    (h : HasApproxInvariantDensities τ) : HasDiagonalDensities τ := by
  intro F ε hε
  obtain ⟨Y, φ, T, hone, hcp, hT, htr, hτ, hcomm, hmul⟩ := h F ε hε
  obtain ⟨U, μ, hU1, hU2, hD⟩ := exists_unitary_diagonalize hT
  have hTD : T = U * diagonal (fun i ↦ (μ i : ℂ)) * Uᴴ := eq_conj_of_conj_eq hU2 hD
  have hucp := ucp_conjLinear_comp Y Y φ hone hcp U hU1
  have hφB : ∀ x, φ x = U * (conjLinear U ∘ₗ φ) x * Uᴴ := fun x ↦
    eq_conj_of_conj_eq hU2 rfl
  refine ⟨Y, conjLinear U ∘ₗ φ, μ, hucp.1, hucp.2, ?_, ?_, ?_, ?_⟩
  · -- normalisation
    rw [hTD, mul_conj hU1, trace_conj_unitary U _ hU1, trace_diagonal_mul_diagonal] at htr
    first
      | exact_mod_cast htr
      | exact Complex.ofReal_eq_one.mp htr
  · -- trace clause
    intro x hx
    have e : trace (T * φ x * T)
        = ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * (conjLinear U ∘ₗ φ) x i i := by
      rw [hφB x, hTD, mul_conj hU1, mul_conj hU1, trace_conj_unitary U _ hU1,
        trace_diagonal_mul_mul_diagonal]
    have hx' := hτ x hx
    rw [e] at hx'
    exact hx'
  · -- commutator clause
    intro x hx
    have hN : φ x * T - T * φ x
        = U * ((conjLinear U ∘ₗ φ) x * diagonal (fun i ↦ (μ i : ℂ))
          - diagonal (fun i ↦ (μ i : ℂ)) * (conjLinear U ∘ₗ φ) x) * Uᴴ := by
      rw [hφB x, hTD, mul_conj hU1, mul_conj hU1, sub_conj]
    have e : (trace ((φ x * T - T * φ x)ᴴ * (φ x * T - T * φ x))).re
        = ∑ i, ∑ j, Complex.normSq ((conjLinear U ∘ₗ φ) x i j) * (μ j - μ i) ^ 2 := by
      rw [hN, trace_conjTranspose_mul_self_conj U _ hU1, re_trace_conjTranspose_mul_self]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        normSq_commutator_diagonal_apply μ _ i j
    exact e.symm.le.trans (hcomm x hx)
  · -- multiplicativity clause
    intro x hx y hy
    have hN : (φ (x * y) - φ x * φ y) * T
        = U * (((conjLinear U ∘ₗ φ) (x * y) - (conjLinear U ∘ₗ φ) x * (conjLinear U ∘ₗ φ) y)
          * diagonal (fun i ↦ (μ i : ℂ))) * Uᴴ := by
      rw [hφB (x * y), hφB x, hφB y, hTD, mul_conj hU1, sub_conj, mul_conj hU1]
    have e : (trace (((φ (x * y) - φ x * φ y) * T)ᴴ * ((φ (x * y) - φ x * φ y) * T))).re
        = ∑ i, ∑ j, Complex.normSq (((conjLinear U ∘ₗ φ) (x * y)
            - (conjLinear U ∘ₗ φ) x * (conjLinear U ∘ₗ φ) y) i j) * μ j ^ 2 := by
      rw [hN, trace_conjTranspose_mul_self_conj U _ hU1, re_trace_conjTranspose_mul_self]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        normSq_mul_diagonal_apply μ _ i j
    exact e.symm.le.trans (hmul x hx y hy)

end

end GroupApproximation.Full.TWWSchafhauser.Connes
