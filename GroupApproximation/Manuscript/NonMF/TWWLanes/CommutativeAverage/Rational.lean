import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Archimedean
import GroupApproximation.Meta.AxiomGuard

/-!
# Rational point averages approximating a finite convex combination (lane nm-tww-01, part 1)

This is the purely combinatorial half of the partition-of-unity approximation of states on
`C(X)` by averages of point evaluations. Here `t : Fin n → ℝ` holds nonnegative weights
with `∑ t = 1`, and `c : Fin n → X` holds points. Given `η > 0`, we find `N > 0` and
`x : Fin N → X` such that for every `φ : X → ℂ` with `‖φ (c i)‖ ≤ B`,
`‖∑ i, t i φ (c i) - N⁻¹ ∑ j, φ (x j)‖ ≤ η`.

Route:
* `M = K + n` with `K` large, `m i = ⌊M t i⌋₊`, and `N = ∑ m i`, so `M - n ≤ N ≤ M`
  (`floorWeights_bounds`).
* `N t i - m i = (M t i - m i) - (M - N) t i`, and this lies in `[-n, 1)`. Hence
  `|N t i - m i| ≤ n + 1`.
* The points `x` repeat `c i` exactly `m i` times, through `finSigmaFinEquiv`
  (`sum_repeatPoints`).
* `‖∑ t φ - N⁻¹ ∑ m φ‖ = N⁻¹ ‖∑ (N t i - m i) φ (c i)‖ ≤ N⁻¹ n (n+1) B`
  (`norm_weighted_sub_average_le`), and `N ≥ K > n(n+1)B/η`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CommutativeAverage

noncomputable section

/-- Floor multiplicities `⌊M t i⌋₊`. -/
def floorWeights {n : ℕ} (M : ℝ) (t : Fin n → ℝ) (i : Fin n) : ℕ :=
  ⌊M * t i⌋₊

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.floorWeights

/-- The list of points in which `c i` is repeated `m i` times. -/
def repeatPoints {X : Type*} {n : ℕ} (c : Fin n → X) (m : Fin n → ℕ)
    (j : Fin (∑ i, m i)) : X :=
  c ((finSigmaFinEquiv (m := n) (n := m)).symm j).1

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.repeatPoints

/-- Summing over the repeated points counts each `c i` with multiplicity `m i`. -/
theorem sum_repeatPoints {X : Type*} {n : ℕ} (c : Fin n → X) (m : Fin n → ℕ)
    (φ : X → ℂ) :
    ∑ j, φ (repeatPoints c m j) = ∑ i, (m i : ℂ) * φ (c i) := by
  calc
    ∑ j, φ (repeatPoints c m j)
        = ∑ p : (i : Fin n) × Fin (m i), φ (c p.1) :=
      Equiv.sum_comp (finSigmaFinEquiv (m := n) (n := m)).symm
        (fun p : (i : Fin n) × Fin (m i) => φ (c p.1))
    _ = ∑ i, ∑ _k : Fin (m i), φ (c i) :=
      Fintype.sum_sigma (fun p : (i : Fin n) × Fin (m i) => φ (c p.1))
    _ = ∑ i, (m i : ℂ) * φ (c i) :=
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.sum_repeatPoints

/-- The floor counts have total at least `M - n`, and each defect
`|N t i - m i|` is at most `n + 1`. -/
theorem floorWeights_bounds {n : ℕ} (t : Fin n → ℝ) (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∑ i, t i = 1) {M : ℝ} (hM : 0 ≤ M) :
    M - n ≤ ((∑ i, floorWeights M t i : ℕ) : ℝ) ∧
      ∀ i, |((∑ k, floorWeights M t k : ℕ) : ℝ) * t i - (floorWeights M t i : ℝ)|
        ≤ n + 1 := by
  have hle : ∀ i, (floorWeights M t i : ℝ) ≤ M * t i := fun i =>
    Nat.floor_le (mul_nonneg hM (ht0 i))
  have hgt : ∀ i, M * t i < (floorWeights M t i : ℝ) + 1 := fun i =>
    Nat.lt_floor_add_one _
  have hNcast : ((∑ i, floorWeights M t i : ℕ) : ℝ) = ∑ i, (floorWeights M t i : ℝ) :=
    Nat.cast_sum _ _
  have hMsum : M = ∑ i, M * t i := by rw [← Finset.mul_sum, ht1, mul_one]
  have hdef : M - ((∑ i, floorWeights M t i : ℕ) : ℝ) =
      ∑ i, (M * t i - (floorWeights M t i : ℝ)) := by
    rw [hNcast, Finset.sum_sub_distrib, ← hMsum]
  have hgap0 : 0 ≤ M - ((∑ i, floorWeights M t i : ℕ) : ℝ) := by
    rw [hdef]
    exact Finset.sum_nonneg fun i _ => sub_nonneg.2 (hle i)
  have hgapn : M - ((∑ i, floorWeights M t i : ℕ) : ℝ) ≤ n := by
    rw [hdef]
    calc
      ∑ i, (M * t i - (floorWeights M t i : ℝ)) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by linarith [hgt i]
      _ = n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  refine ⟨by linarith [hgapn], fun i => ?_⟩
  have ht1i : t i ≤ 1 := by
    rw [← ht1]
    exact Finset.single_le_sum (fun k _ => ht0 k) (Finset.mem_univ i)
  have p1 : 0 ≤ (M - ((∑ k, floorWeights M t k : ℕ) : ℝ)) * t i :=
    mul_nonneg hgap0 (ht0 i)
  have p2 : (M - ((∑ k, floorWeights M t k : ℕ) : ℝ)) * t i ≤ n :=
    le_trans (mul_le_of_le_one_right hgap0 ht1i) hgapn
  have e : ((∑ k, floorWeights M t k : ℕ) : ℝ) * t i - (floorWeights M t i : ℝ) =
      (M * t i - (floorWeights M t i : ℝ)) -
        (M - ((∑ k, floorWeights M t k : ℕ) : ℝ)) * t i := by
    ring
  rw [e, abs_le]
  constructor
  · linarith [hle i, p2]
  · linarith [hgt i, p1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.floorWeights_bounds

/-- Replacing the weights `t i` by `m i / N` costs at most `N⁻¹ · n · C · B`
when `|N t i - m i| ≤ C` and `‖a i‖ ≤ B`. -/
theorem norm_weighted_sub_average_le {n N : ℕ} (hN : 0 < N) (t : Fin n → ℝ)
    (m : Fin n → ℕ) (a : Fin n → ℂ) {C B : ℝ}
    (hC : ∀ i, |(N : ℝ) * t i - (m i : ℝ)| ≤ C) (ha : ∀ i, ‖a i‖ ≤ B) (hC0 : 0 ≤ C) :
    ‖∑ i, (t i : ℂ) * a i - (N : ℂ)⁻¹ * ∑ i, (m i : ℂ) * a i‖ ≤
      (N : ℝ)⁻¹ * (n * (C * B)) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have key : ∑ i, (((N : ℝ) * t i - (m i : ℝ) : ℝ) : ℂ) * a i =
      (N : ℂ) * ∑ i, (t i : ℂ) * a i - ∑ i, (m i : ℂ) * a i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hdiff : ∑ i, (t i : ℂ) * a i - (N : ℂ)⁻¹ * ∑ i, (m i : ℂ) * a i =
      (N : ℂ)⁻¹ * ∑ i, (((N : ℝ) * t i - (m i : ℝ) : ℝ) : ℂ) * a i := by
    rw [key, mul_sub, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg N))
  calc
    ‖∑ i, (((N : ℝ) * t i - (m i : ℝ) : ℝ) : ℂ) * a i‖
        ≤ ∑ i, ‖(((N : ℝ) * t i - (m i : ℝ) : ℝ) : ℂ) * a i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, C * B :=
      Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hC i) (ha i) (norm_nonneg _) hC0
    _ = n * (C * B) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.norm_weighted_sub_average_le

/-- A finite convex combination of point values is uniformly approximated by a rational
average of point values, over every function bounded by `B` at the points. -/
theorem exists_average_approx {X : Type*} {n : ℕ} (c : Fin n → X) (t : Fin n → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∑ i, t i = 1) (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (_ : 0 < N) (x : Fin N → X), ∀ φ : X → ℂ, (∀ i, ‖φ (c i)‖ ≤ B) →
      ‖∑ i, (t i : ℂ) * φ (c i) - (N : ℂ)⁻¹ * ∑ j, φ (x j)‖ ≤ η := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max ((n : ℝ) * (((n : ℝ) + 1) * B) / η) 0)
  have hM : (0 : ℝ) ≤ (K : ℝ) + n := by positivity
  obtain ⟨hNlow, hcount⟩ := floorWeights_bounds t ht0 ht1 hM
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hCK : (n : ℝ) * (((n : ℝ) + 1) * B) / η < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hNreal : (K : ℝ) ≤ ((∑ i, floorWeights ((K : ℝ) + n) t i : ℕ) : ℝ) := by
    linarith [hNlow]
  have hNpos : 0 < ∑ i, floorWeights ((K : ℝ) + n) t i :=
    Nat.cast_pos.1 (lt_of_lt_of_le hKpos hNreal)
  refine ⟨∑ i, floorWeights ((K : ℝ) + n) t i, hNpos,
    repeatPoints c (floorWeights ((K : ℝ) + n) t), fun φ hφ => ?_⟩
  rw [sum_repeatPoints c (floorWeights ((K : ℝ) + n) t) φ]
  refine le_trans (norm_weighted_sub_average_le hNpos t (floorWeights ((K : ℝ) + n) t)
    (fun i => φ (c i)) hcount hφ (by positivity)) ?_
  rw [inv_mul_le_iff₀ (Nat.cast_pos.2 hNpos)]
  have h1 : (n : ℝ) * (((n : ℝ) + 1) * B) < K * η := (div_lt_iff₀ hη).1 hCK
  have h2 : (K : ℝ) * η ≤ ((∑ i, floorWeights ((K : ℝ) + n) t i : ℕ) : ℝ) * η :=
    mul_le_mul_of_nonneg_right hNreal hη.le
  linarith [h1, h2]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.exists_average_approx

end

end CommutativeAverage
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
