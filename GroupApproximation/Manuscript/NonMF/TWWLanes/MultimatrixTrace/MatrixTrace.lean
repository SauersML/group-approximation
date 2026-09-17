import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Tracial functionals on a full matrix algebra (lane nm-tww-03, part 1)

Two facts about `M_k(ℂ)`, used by the multimatrix trace theorem.

* `exists_apply_eq_trace_mul`: a linear functional `φ` with `φ(xy) = φ(yx)` is a scalar
  multiple of the trace. For `i ≠ j`, `E_ij = E_ii E_ij` and `E_ij E_ii = 0` give
  `φ(E_ij) = 0`. Also `E_ii = E_ij E_ji` and `E_jj = E_ji E_ij` give `φ(E_ii) = φ(E_jj)`.
  Expand `x = ∑ x_ij E_ij`. For `k = 0` the algebra is zero.
* `apply_eq_mul_trace_div`: then `φ x = φ 1 · (trace x / k)`. This also holds for `k = 0`,
  where both sides vanish.
* `norm_trace_div_le`: `‖trace x / k‖ ≤ ‖x‖` for the L2 operator norm. For `k > 0` it is
  `KazhdanCornerMatrices.norm_normTrace_le_l2_opNorm` on the finite model `Fin k`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace MultimatrixTrace

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **A tracial functional on `M_k(ℂ)` is a multiple of the trace.** -/
theorem exists_apply_eq_trace_mul {k : ℕ} (φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] ℂ)
    (hφ : ∀ x y, φ (x * y) = φ (y * x)) :
    ∃ d : ℂ, ∀ x : Matrix (Fin k) (Fin k) ℂ, φ x = Matrix.trace x * d := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, fun x ↦ ?_⟩
    have hx : x = 0 := Matrix.ext fun i _ ↦ i.elim0
    rw [hx, map_zero, mul_zero]
  · obtain ⟨d, hd⟩ : ∃ d : ℂ, φ (Matrix.single (⟨0, hk⟩ : Fin k) ⟨0, hk⟩ 1) = d := ⟨_, rfl⟩
    have hoff : ∀ (i j : Fin k) (c : ℂ), i ≠ j → φ (Matrix.single i j c) = 0 := by
      intro i j c hij
      have ha : Matrix.single i i (1 : ℂ) * Matrix.single i j c = Matrix.single i j c := by
        rw [Matrix.single_mul_single_same, one_mul]
      have hb : Matrix.single i j c * Matrix.single i i (1 : ℂ) = 0 :=
        Matrix.single_mul_single_of_ne c i j i (fun h ↦ hij h.symm) 1
      rw [← ha, hφ, hb, map_zero]
    have hdiag : ∀ (i : Fin k) (c : ℂ), φ (Matrix.single i i c) = c * d := by
      intro i c
      have h1 : Matrix.single i i c = c • Matrix.single i i (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have ha : Matrix.single i ⟨0, hk⟩ (1 : ℂ) * Matrix.single ⟨0, hk⟩ i (1 : ℂ) =
          Matrix.single i i 1 := by
        rw [Matrix.single_mul_single_same, mul_one]
      have hb : Matrix.single ⟨0, hk⟩ i (1 : ℂ) * Matrix.single i ⟨0, hk⟩ (1 : ℂ) =
          Matrix.single ⟨0, hk⟩ ⟨0, hk⟩ 1 := by
        rw [Matrix.single_mul_single_same, mul_one]
      have h2 : φ (Matrix.single i i (1 : ℂ)) = d := by
        rw [← ha, hφ, hb, hd]
      rw [h1, map_smul, smul_eq_mul, h2]
    refine ⟨d, fun x ↦ ?_⟩
    calc φ x = φ (∑ i : Fin k, ∑ j : Fin k, Matrix.single i j (x i j)) := by
          rw [← Matrix.matrix_eq_sum_single x]
      _ = ∑ i : Fin k, ∑ j : Fin k, φ (Matrix.single i j (x i j)) := by
          simp only [map_sum]
      _ = ∑ i : Fin k, x i i * d := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_eq_single i (fun j _ hji ↦ hoff i j (x i j) (Ne.symm hji))
            (fun hi ↦ absurd (Finset.mem_univ i) hi)]
          exact hdiag i (x i i)
      _ = Matrix.trace x * d := by
          rw [← Finset.sum_mul]
          rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.exists_apply_eq_trace_mul

/-- **Normalized form.** A tracial functional on `M_k(ℂ)` is `φ 1` times the normalized
trace `trace x / k`. -/
theorem apply_eq_mul_trace_div {k : ℕ} (φ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] ℂ)
    (hφ : ∀ x y, φ (x * y) = φ (y * x)) (x : Matrix (Fin k) (Fin k) ℂ) :
    φ x = φ 1 * (Matrix.trace x / (k : ℂ)) := by
  obtain ⟨d, hd⟩ := exists_apply_eq_trace_mul φ hφ
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hx : x = 0 := Matrix.ext fun i _ ↦ i.elim0
    rw [hx, map_zero, Nat.cast_zero, div_zero, mul_zero]
  · have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rw [hd x, hd 1, Matrix.trace_one, Fintype.card_fin, mul_comm (k : ℂ) d, mul_assoc,
      mul_div_cancel₀ _ hk0, mul_comm]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.apply_eq_mul_trace_div

/-- **The normalized trace is contractive** for the L2 operator norm. -/
theorem norm_trace_div_le (k : ℕ) (x : Matrix (Fin k) (Fin k) ℂ) :
    ‖Matrix.trace x / (k : ℂ)‖ ≤ ‖x‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, div_zero, norm_zero]
    exact norm_nonneg x
  · have hY : 0 < Fintype.card (⟨Fin k, inferInstance, inferInstance⟩ : FiniteModel) := by
      change 0 < Fintype.card (Fin k)
      rw [Fintype.card_fin]
      exact hk
    have h := KazhdanCornerMatrices.norm_normTrace_le_l2_opNorm
      ⟨Fin k, inferInstance, inferInstance⟩ hY x
    change ‖Matrix.trace x / ((Fintype.card (Fin k) : ℕ) : ℂ)‖ ≤ ‖x‖ at h
    rwa [Fintype.card_fin] at h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.norm_trace_div_le

end

end MultimatrixTrace
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
