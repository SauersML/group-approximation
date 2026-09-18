import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseSqrt
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-25, part 5: `ContractionSqrtCommutatorStatement → HasSqrtCommutatorControl A`

Fix a unital `A`, a finite `F` and `ε > 0`.

1. Write each `x` as `∑ᵢ cᵢ(x) uᵢ(x)` with four unitaries and `|cᵢ(x)| ≤ ‖x‖/2`.
2. Choose `R ≥ 1` with `‖x‖² ≤ R` on `F`, and put `ε' = ε / (8R)`.  Let `η` be the
   tolerance from the smaller Statement at `ε'`.
3. Let `F'` be the set of all `uᵢ(x)` and `uᵢ(x)⋆` for `x ∈ F`.
4. Given `ρ` and `h`, take the positive square root `T` of `h`.  For each unitary,
   `y = ρ(uᵢ)` is a contraction.  Weak multiplicativity at `(uᵢ⋆, uᵢ)` and `(uᵢ, uᵢ⋆)`
   gives `tr(h(1 − y⋆y))` and `tr(h(1 − yy⋆))`, because `ρ 1 = 1` and `ρ` preserves stars.
   So `‖ρ(uᵢ)T − Tρ(uᵢ)‖₂² ≤ ε'`.
5. The commutator is linear in `x`.  The parallelogram law gives
   `‖ρ(x)T − Tρ(x)‖₂² ≤ 22 (‖x‖/2)² ε' ≤ 8Rε' = ε`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **The `sqrtControl` reduction.**  Powers--Størmer control for one contraction implies
`HasSqrtCommutatorControl A` on every unital C⋆-algebra `A`. -/
theorem hasSqrtCommutatorControl_of_contraction (hC : ContractionSqrtCommutatorStatement)
    (A : Type u) [CStarAlgebra A] : HasSqrtCommutatorControl A := by
  classical
  intro F ε hε
  choose U c hUc hc using fun x : A ↦ CStarAlgebra.exists_sum_four_unitary x
  have hun : ∀ v : unitary A, ‖(v : A)‖ ≤ 1 := fun v ↦ by
    rcases subsingleton_or_nontrivial A with hA | hA
    · letI : Subsingleton A := hA
      rw [Subsingleton.elim (v : A) 0, norm_zero]
      exact zero_le_one
    · letI : Nontrivial A := hA
      exact le_of_eq (CStarRing.norm_of_mem_unitary v.property)
  obtain ⟨R, hR1, hRF⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ z ∈ F, ‖z‖ ^ 2 ≤ R := by
    refine ⟨1 + ∑ x ∈ F, ‖x‖ ^ 2, ?_, fun z hz ↦ ?_⟩
    · have hs : 0 ≤ ∑ x ∈ F, ‖x‖ ^ 2 := Finset.sum_nonneg fun x _ ↦ sq_nonneg ‖x‖
      linarith
    · have hs : ‖z‖ ^ 2 ≤ ∑ x ∈ F, ‖x‖ ^ 2 :=
        Finset.single_le_sum (fun x _ ↦ sq_nonneg ‖x‖) hz
      linarith
  have hden : 0 < 8 * R := by linarith
  obtain ⟨ε', hε', hε'eq⟩ : ∃ ε' : ℝ, 0 < ε' ∧ 8 * R * ε' = ε :=
    ⟨ε / (8 * R), div_pos hε hden, mul_div_cancel₀ ε hden.ne'⟩
  obtain ⟨η, hη, hCη⟩ := hC ε' hε'
  obtain ⟨F', hF'u, hF's⟩ : ∃ F' : Finset A, (∀ x ∈ F, ∀ i, (U x i : A) ∈ F') ∧
      (∀ x ∈ F, ∀ i, star (U x i : A) ∈ F') := by
    refine ⟨F.biUnion (fun x ↦ Finset.univ.image fun i ↦ (U x i : A))
      ∪ F.biUnion (fun x ↦ Finset.univ.image fun i ↦ star (U x i : A)), ?_, ?_⟩
    · intro x hx i
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_image_of_mem (fun j ↦ (U x j : A)) (Finset.mem_univ i)⟩)
    · intro x hx i
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_image_of_mem (fun j ↦ star (U x j : A)) (Finset.mem_univ i)⟩)
  refine ⟨F', η, hη, ?_⟩
  intro Y ρ hρ1 hρn hρs h hh htr hcomm hmul
  obtain ⟨T, hTpsd, hTT⟩ := exists_posSemidef_mul_self_eq Y hh
  refine ⟨T, hTpsd.1, hTT, fun x hx ↦ ?_⟩
  have hU : ∀ i, (Matrix.trace ((ρ (U x i : A) * T - T * ρ (U x i : A))ᴴ
      * (ρ (U x i : A) * T - T * ρ (U x i : A)))).re ≤ ε' := fun i ↦ by
    have h1 := hmul (star (U x i : A)) (hF's x hx i) (U x i : A) (hF'u x hx i)
    rw [Unitary.star_mul_self_of_mem (U x i).2, hρ1, hρs] at h1
    have h2 := hmul (U x i : A) (hF'u x hx i) (star (U x i : A)) (hF's x hx i)
    rw [Unitary.mul_star_self_of_mem (U x i).2, hρ1, hρs] at h2
    exact hCη Y (ρ (U x i : A)) h T ((hρn _).trans (hun _)) hTpsd hTT htr
      (hcomm _ (hF'u x hx i)) h1 h2
  have hcx : ∀ i, Complex.normSq (c x i) ≤ (‖x‖ / 2) ^ 2 := fun i ↦ by
    rw [← Complex.sq_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc x i) 2
  have ex : x = c x 0 • (U x 0 : A) + c x 1 • (U x 1 : A) + c x 2 • (U x 2 : A)
      + c x 3 • (U x 3 : A) := (hUc x).trans (Fin.sum_univ_four _)
  rw [commutator_eq_four ρ T (c x) (fun i ↦ (U x i : A)) ex]
  refine (re_trace_gram_four_le (c x) (fun i ↦ ρ (U x i : A) * T - T * ρ (U x i : A))
    hcx hU).trans ?_
  have hxR : ‖x‖ ^ 2 * ε' ≤ R * ε' := mul_le_mul_of_nonneg_right (hRF x hx) hε'.le
  have hRε : 0 ≤ R * ε' := mul_nonneg (by linarith) hε'.le
  have hfin : 22 * ((‖x‖ / 2) ^ 2 * ε') = 11 / 2 * (‖x‖ ^ 2 * ε') := by ring
  rw [hfin]
  linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.hasSqrtCommutatorControl_of_contraction

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
