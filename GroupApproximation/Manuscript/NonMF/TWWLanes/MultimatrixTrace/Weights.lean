import GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.MatrixTrace
import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Presentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Tracial states on a multimatrix algebra are convex combinations of block traces
(lane nm-tww-03, part 2)

Let `B = ⊕_{i<r} M_{k_i}(ℂ)` (`AFQD.Multimatrix r k`) and let `τ` be a tracial state on `B`.
Then there are weights `t : Fin r → ℝ` with `t i ≥ 0` and `∑ t i = 1` such that
`τ b = ∑ t i · trace(b i) / k i`. This is the first clause of the lane, with
`normTrace (b i)` spelled `Matrix.trace (b i) / (k i : ℂ)`, which is how the downstream
Statement `AFQD.MultimatrixTraceAmplificationStatement` spells the normalized trace.
The weights also vanish on empty blocks.

## Route

* For each block `i`, the functional `x ↦ τ(Pi.single i x)` on `M_{k_i}` is tracial,
  because `Pi.single i` is multiplicative. So it equals `τ(e_i) · trace x / k_i`, where
  `e_i = Pi.single i 1` (`apply_eq_mul_trace_div`).
* `e_i = e_i⋆ e_i`, so `τ(e_i) ≥ 0` in the complex order. Hence `τ(e_i)` is the real
  number `t i := re τ(e_i) ≥ 0`.
* `b = ∑ Pi.single i (b i)` gives the formula. At `b = 1` it gives `∑ τ(e_i) = 1`.
* If `k i = 0` then `e_i = 0`, so `t i = 0`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace MultimatrixTrace

open scoped ComplexOrder

noncomputable section

/-- **Clause 1 of lane `nm-tww-03`.** Every tracial state on `⊕ M_{k_i}(ℂ)` is a convex
combination `∑ t i · trace(b i) / k i` of the normalized block traces. The weights vanish
on empty blocks. -/
theorem exists_weights (r : ℕ) (k : Fin r → ℕ) (τ : TracialState (AFQD.Multimatrix r k)) :
    ∃ t : Fin r → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧ (∀ i, k i = 0 → t i = 0) ∧
      ∀ b : AFQD.Multimatrix r k,
        τ b = ∑ i, (t i : ℂ) * (Matrix.trace (b i) / (k i : ℂ)) := by
  have hsingle : ∀ (i : Fin r) (x : Matrix (Fin (k i)) (Fin (k i)) ℂ),
      τ (Pi.single i x : AFQD.Multimatrix r k) =
        τ (Pi.single i 1 : AFQD.Multimatrix r k) * (Matrix.trace x / (k i : ℂ)) := by
    intro i x
    let φ : Matrix (Fin (k i)) (Fin (k i)) ℂ →ₗ[ℂ] ℂ :=
      τ.toLinearMap.comp
        (LinearMap.single ℂ (fun j : Fin r ↦ Matrix (Fin (k j)) (Fin (k j)) ℂ) i)
    have hφ : ∀ a c, φ (a * c) = φ (c * a) := by
      intro a c
      change τ (Pi.single i (a * c) : AFQD.Multimatrix r k) =
        τ (Pi.single i (c * a) : AFQD.Multimatrix r k)
      rw [Pi.single_mul, Pi.single_mul]
      exact τ.map_mul_comm _ _
    exact apply_eq_mul_trace_div φ hφ x
  have he : ∀ i : Fin r, star (Pi.single i 1 : AFQD.Multimatrix r k) * Pi.single i 1 =
      (Pi.single i 1 : AFQD.Multimatrix r k) := by
    intro i
    rw [← Pi.single_star, ← Pi.single_mul, star_one, one_mul]
  have hnonneg : ∀ i : Fin r, 0 ≤ τ (Pi.single i 1 : AFQD.Multimatrix r k) := by
    intro i
    have h := τ.map_star_mul_self_nonneg (Pi.single i 1 : AFQD.Multimatrix r k)
    rw [he i] at h
    exact h
  have hz : ∀ i : Fin r, τ (Pi.single i 1 : AFQD.Multimatrix r k) =
      ((τ (Pi.single i 1 : AFQD.Multimatrix r k)).re : ℂ) := by
    intro i
    refine Complex.eq_re_of_ofReal_le (r := 0) ?_
    rw [Complex.ofReal_zero]
    exact hnonneg i
  have hsum : ∀ b : AFQD.Multimatrix r k,
      τ b = ∑ i, τ (Pi.single i (b i) : AFQD.Multimatrix r k) := by
    intro b
    calc τ b = τ (∑ i, (Pi.single i (b i) : AFQD.Multimatrix r k)) := by
          rw [Finset.univ_sum_single b]
      _ = ∑ i, τ (Pi.single i (b i) : AFQD.Multimatrix r k) :=
          map_sum τ.toLinearMap _ _
  have hone : ∑ i, τ (Pi.single i 1 : AFQD.Multimatrix r k) = 1 :=
    (hsum 1).symm.trans τ.map_one
  refine ⟨fun i ↦ (τ (Pi.single i 1 : AFQD.Multimatrix r k)).re, fun i ↦ ?_, ?_,
    fun i hi ↦ ?_, fun b ↦ ?_⟩
  · exact (Complex.nonneg_iff.mp (hnonneg i)).1
  · have h := congrArg Complex.re hone
    rw [Complex.re_sum, Complex.one_re] at h
    exact h
  · have h1 : (1 : Matrix (Fin (k i)) (Fin (k i)) ℂ) = 0 :=
      Matrix.ext fun a _ ↦ (Nat.not_lt_zero a.val (lt_of_lt_of_eq a.isLt hi)).elim
    change (τ (Pi.single i 1 : AFQD.Multimatrix r k)).re = 0
    rw [h1, Pi.single_zero, TracialState.map_zero, Complex.zero_re]
  · rw [hsum b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hsingle i (b i)]
    exact congrArg (· * (Matrix.trace (b i) / (k i : ℂ))) (hz i)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.exists_weights

end

end MultimatrixTrace
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
