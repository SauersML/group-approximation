import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import GroupApproximation.GroupTheory.HigmanThompson.ResidueInvariance
import GroupApproximation.Meta.AxiomGuard

/-!
# Telescoping residues along the grid

The tools behind Hyde–Lodha's Lemma 3.9(5) at `x = 0`: along an interval subdivided at level-`L`
grid points, a piecewise linear map with slopes `n^i · r` changes `f t - r t` only within its
residue class modulo `(n - 1) ℤ[1/n]`, `n = m + 2` (`HigmanThompson.ResEq`).

* `resEq_of_sub_eq`: `ResEq m x y` depends only on `x - y`.
* `resEq_telescope`: residues telescope along a sequence.
* `resEq_of_affineOn_pow`: on one affine piece of slope `n^i r` with grid length, `f t - r t` keeps
  its residue (`resEq_pow_mul`).
* `slope_eq_of_affineOn`: two affine pieces around one point have equal slopes.
* `not_mem_grid_fifth`, `gridPt_lt_fifth`, `fifth_lt_gridPt_succ`: the point
  `(5k + 1) / (5 · 6^L)` lies strictly inside the level-`L` grid interval `[k/6^L, (k+1)/6^L]` and
  outside `ℤ[1/6]`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

section Residues

variable {m : ℕ}

/-- `ResEq m x y` depends only on `x - y`. -/
theorem resEq_of_sub_eq {x y x' y' : ℚ} (h : ResEq m x' y') (e : x - y = x' - y') :
    ResEq m x y := by
  obtain ⟨N, k, hk⟩ := h
  exact ⟨N, k, by rw [e]; exact hk⟩

/-- **Residues telescope** along a sequence. -/
theorem resEq_telescope (g : ℤ → ℚ) (k₀ : ℤ) (j : ℕ)
    (hstep : ∀ i : ℕ, i < j → ResEq m (g (k₀ + i + 1)) (g (k₀ + i))) :
    ResEq m (g (k₀ + j)) (g k₀) := by
  induction j with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact ResEq.refl _
  | succ j ih =>
    have e : k₀ + ((j + 1 : ℕ) : ℤ) = k₀ + (j : ℤ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc]
    rw [e]
    exact ResEq.trans (hstep j (Nat.lt_succ_self j))
      (ih fun i hi => hstep i (Nat.lt_succ_of_lt hi))

/-- **One affine piece.**  If `f` is affine on `[p, q]` with slope `n^i r` and `q - p ∈ ℤ[1/n]`,
then `f q - r q ≡ f p - r p`. -/
theorem resEq_of_affineOn_pow {f : ℚ → ℚ} {p q : ℚ} {i r : ℤ} (hpq : p ≤ q)
    (haff : AffineOn f p q (((m : ℚ) + 2) ^ i * r)) {M : ℕ} (hε : q - p ∈ Grid (m + 2) M) :
    ResEq m (f q - r * q) (f p - r * p) := by
  have hrε : (r : ℚ) * (q - p) ∈ Grid (m + 2) (0 + M) := grid_mul (int_mem_grid 0 r) hε
  obtain ⟨N, k, hk⟩ := resEq_pow_mul (m := m) i ⟨_, hrε⟩
  refine ⟨N, k, ?_⟩
  rw [haff q hpq le_rfl]
  linear_combination hk

end Residues

/-- **Slopes are determined locally**: two affine pieces of `f` around one point have equal slopes. -/
theorem slope_eq_of_affineOn {f : ℚ → ℚ} {a b p q s₁ s₂ x : ℚ} (h₁ : AffineOn f a b s₁)
    (hax : a < x) (hxb : x < b) (h₂ : AffineOn f p q s₂) (hpx : p < x) (hxq : x < q) :
    s₁ = s₂ := by
  obtain ⟨y, hy⟩ : ∃ y : ℚ, y = min b q := ⟨_, rfl⟩
  have hyb : y ≤ b := by
    rw [hy]
    exact min_le_left _ _
  have hyq : y ≤ q := by
    rw [hy]
    exact min_le_right _ _
  have hxy : x < y := by
    rw [hy]
    exact lt_min hxb hxq
  have hy1 := h₁ y (by linarith) hyb
  have hx1 := h₁ x hax.le hxb.le
  have hy2 := h₂ y (by linarith) hyq
  have hx2 := h₂ x hpx.le hxq.le
  have e : (s₁ - s₂) * (y - x) = 0 := by
    linear_combination hx1 - hy1 + hy2 - hx2
  rcases mul_eq_zero.mp e with h0 | h0
  · linarith
  · linarith

/-! ## A point outside `ℤ[1/6]` in every grid interval -/

/-- `(5k + 1) / (5 · 6^L) ∉ ℤ[1/6]`. -/
theorem not_mem_grid_fifth (L : ℕ) (k : ℤ) (M : ℕ) :
    ((5 * k + 1 : ℤ) : ℚ) / (5 * (6 : ℚ) ^ L) ∉ Grid 6 M := by
  rintro ⟨K, hK⟩
  have hpos : (5 : ℚ) * (6 : ℚ) ^ L ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hpos] at hK
  have hz : (5 * k + 1) * 6 ^ M = K * (5 * 6 ^ L) := by exact_mod_cast hK
  have hdvd : (5 : ℤ) ∣ (5 * k + 1) * 6 ^ M := ⟨K * 6 ^ L, by rw [hz]; ring⟩
  have hcop : IsCoprime (5 : ℤ) (6 ^ M) := IsCoprime.pow_right ⟨-1, 1, by norm_num⟩
  have h5 := hcop.dvd_of_dvd_mul_right hdvd
  omega

theorem gridPt_lt_fifth (L : ℕ) (k : ℤ) :
    gridPt 6 L k < ((5 * k + 1 : ℤ) : ℚ) / (5 * (6 : ℚ) ^ L) := by
  have h6 : (0 : ℚ) < (6 : ℚ) ^ L := by positivity
  unfold gridPt
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

theorem fifth_lt_gridPt_succ (L : ℕ) (k : ℤ) :
    ((5 * k + 1 : ℤ) : ℚ) / (5 * (6 : ℚ) ^ L) < gridPt 6 L (k + 1) := by
  have h6 : (0 : ℚ) < (6 : ℚ) ^ L := by positivity
  unfold gridPt
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

#audit_axioms GroupApproximation.HydeLodha.resEq_telescope
#audit_axioms GroupApproximation.HydeLodha.resEq_of_affineOn_pow
#audit_axioms GroupApproximation.HydeLodha.slope_eq_of_affineOn
#audit_axioms GroupApproximation.HydeLodha.not_mem_grid_fifth
#audit_axioms GroupApproximation.HydeLodha.gridPt_lt_fifth
#audit_axioms GroupApproximation.HydeLodha.fifth_lt_gridPt_succ

end HydeLodha
end GroupApproximation
