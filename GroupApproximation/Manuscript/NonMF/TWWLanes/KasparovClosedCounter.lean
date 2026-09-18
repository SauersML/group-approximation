import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosedFinSupp
import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Series
import GroupApproximation.Meta.AxiomGuard

/-!
# Closing Kasparov stabilization, lane `nm-tww-24`: `c₀₀(B)` is a counterexample

For a unital C⋆-algebra `B`:

* `c00_isCountablyGenerated`: `c₀₀(B)` is countably generated. The vectors
  `c00Single k 1` generate it. Every vector is *exactly* a finite combination of them.
* `not_isCompleteModule_c00`: if `B` is nontrivial, `c₀₀(B)` is not complete. The partial
  sums of `∑ₙ 2⁻ⁿ • single n 1` are Cauchy (`isCauchy_partialSum`). A limit `y` has
  support below some `N`. Coordinate `N` of `partial sum - y` is `2⁻ᴺ • 1`, so the
  distance stays at least `2⁻ᴺ ‖1‖ > 0` (`norm_coord_le`).
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovClosed

open GroupApproximation.HilbertModule GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

universe v

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **`c₀₀(B)` is countably generated.** -/
theorem c00_isCountablyGenerated : IsCountablyGenerated (c00 B) := by
  refine ⟨fun k => c00Single k 1, fun y ε hε => ?_⟩
  obtain ⟨N, hN⟩ := (mem_finSupp y.1).mp y.2
  refine ⟨N, fun j => y.1.1 j, fun j => j.val, ?_⟩
  have hy : y = ∑ j : Fin N, (c00 B).act (c00Single j.val 1) (y.1.1 j) := by
    refine Subtype.ext (Subtype.ext (funext fun i => ?_))
    have hs := c00_coe_sum_apply (Finset.univ : Finset (Fin N))
      (fun j => (c00 B).act (c00Single j.val 1) (y.1.1 j)) i
    refine Eq.trans ?_ hs.symm
    by_cases hi : i < N
    · refine Eq.trans ?_ (Finset.sum_eq_single (⟨i, hi⟩ : Fin N) ?_ ?_).symm
      · show y.1.1 i = (KasparovStab.single i (1 : B)).1 i * y.1.1 i
        rw [KasparovStab.single_coe_self, one_mul]
      · intro j _ hj
        show (KasparovStab.single j.val (1 : B)).1 i * y.1.1 j = 0
        rw [KasparovStab.single_coe_of_ne (n := j.val) (i := i) (1 : B)
          (fun h => hj (Fin.ext h.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · refine (hN i (not_lt.mp hi)).trans ?_
      refine Eq.symm (Finset.sum_eq_zero ?_)
      intro j _
      show (KasparovStab.single j.val (1 : B)).1 i * y.1.1 j = 0
      have hj := j.isLt
      rw [KasparovStab.single_coe_of_ne (n := j.val) (i := i) (1 : B) (by omega), zero_mul]
  have h0 : (c00 B).norm
      (y - ∑ j : Fin N, (c00 B).act (c00Single j.val 1) (y.1.1 j)) = 0 := by
    rw [← hy, sub_self]
    exact (c00 B).norm_zero_vector
  show (c00 B).norm (y - ∑ j : Fin N, (c00 B).act (c00Single j.val 1) (y.1.1 j)) ≤ ε
  rw [h0]
  exact hε.le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.c00_isCountablyGenerated

/-- The `n`-th term `2⁻ⁿ • single n 1` of the non-convergent series. -/
noncomputable def geomTerm (B : Type v) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (n : ℕ) : (c00 B).carrier :=
  c00Single n ((((2⁻¹ : ℝ) ^ n : ℝ) : ℂ) • (1 : B))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.geomTerm

theorem norm_geomTerm (n : ℕ) :
    (c00 B).norm (geomTerm B n) = (2⁻¹ : ℝ) ^ n * ‖(1 : B)‖ := by
  show (standardModule ℕ B).norm
      (KasparovStab.single n ((((2⁻¹ : ℝ) ^ n : ℝ) : ℂ) • (1 : B))) = _
  rw [KasparovStab.norm_single, norm_smul,
    Complex.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.norm_geomTerm

/-- **`c₀₀(B)` is not complete** for nontrivial unital `B`. -/
theorem not_isCompleteModule_c00 [Nontrivial B] : ¬ IsCompleteModule (c00 B) := by
  intro hc
  have h1 : 0 < ‖(1 : B)‖ := norm_pos_iff.mpr one_ne_zero
  have hsum : Summable fun n : ℕ => (2⁻¹ : ℝ) ^ n * ‖(1 : B)‖ :=
    (summable_geometric_of_lt_one (r := 2⁻¹) (by norm_num) (by norm_num)).mul_right _
  have hcau : IsCauchy (c00 B) fun K => ∑ n ∈ Finset.range K, geomTerm B n :=
    isCauchy_partialSum (fun n => geomTerm B n) hsum fun n => (norm_geomTerm n).le
  obtain ⟨y, hy⟩ := hc _ hcau
  obtain ⟨N, hN⟩ := (mem_finSupp y.1).mp y.2
  have hδ : 0 < (2⁻¹ : ℝ) ^ N * ‖(1 : B)‖ := mul_pos (pow_pos (by norm_num) N) h1
  obtain ⟨M, hM⟩ := hy _ (half_pos hδ)
  have hn : (c00 B).norm ((∑ n ∈ Finset.range (max M (N + 1)), geomTerm B n) - y)
      ≤ (2⁻¹ : ℝ) ^ N * ‖(1 : B)‖ / 2 := hM (max M (N + 1)) (le_max_left _ _)
  have hK : N < max M (N + 1) := lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _)
  have hsumN : (∑ n ∈ Finset.range (max M (N + 1)), geomTerm B n).1.1 N
      = (((2⁻¹ : ℝ) ^ N : ℝ) : ℂ) • (1 : B) := by
    refine (c00_coe_sum_apply (Finset.range (max M (N + 1))) (fun n => geomTerm B n) N).trans ?_
    refine (Finset.sum_eq_single N ?_ ?_).trans ?_
    · intro n _ hn
      exact KasparovStab.single_coe_of_ne (n := n) (i := N)
        ((((2⁻¹ : ℝ) ^ n : ℝ) : ℂ) • (1 : B)) (Ne.symm hn)
    · intro h
      exact absurd (Finset.mem_range.mpr hK) h
    · exact KasparovStab.single_coe_self N ((((2⁻¹ : ℝ) ^ N : ℝ) : ℂ) • (1 : B))
  have hcoord : ((∑ n ∈ Finset.range (max M (N + 1)), geomTerm B n) - y).1.1 N
      = (((2⁻¹ : ℝ) ^ N : ℝ) : ℂ) • (1 : B) := by
    show (∑ n ∈ Finset.range (max M (N + 1)), geomTerm B n).1.1 N - y.1.1 N = _
    rw [hsumN, hN N le_rfl, sub_zero]
  have hle : ‖(((2⁻¹ : ℝ) ^ N : ℝ) : ℂ) • (1 : B)‖
      ≤ (c00 B).norm ((∑ n ∈ Finset.range (max M (N + 1)), geomTerm B n) - y) := by
    rw [← hcoord]
    exact KasparovStab.norm_coord_le _ N
  rw [norm_smul, Complex.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) N)] at hle
  exact lt_irrefl _ (lt_of_le_of_lt (le_trans hle hn) (half_lt_self hδ))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.not_isCompleteModule_c00

end KasparovClosed
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
