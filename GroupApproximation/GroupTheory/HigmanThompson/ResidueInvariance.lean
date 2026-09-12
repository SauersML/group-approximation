import Mathlib.Algebra.Ring.GeomSum
import GroupApproximation.GroupTheory.HigmanThompson.PLMoves
import GroupApproximation.Meta.AxiomGuard

/-!
# The residue invariant of `F_n`

Hyde–Lodha's map `θ_n : ℤ[1/n] → ℤ/(n-1)`, `k/n^l ↦ k mod (n-1)`, is invariant under `F_n`
(their Lemma 3.8, first part).  Here the invariant is recorded as the relation
`ResEq m x y : x - y ∈ (n-1) ℤ[1/n]` of `PLMoves`, for `n = m + 2`.

* `resEq_apply_of_fix`: a grid-affine permutation over `(ℤ[1/n], n^ℤ)` fixing `(-∞, 0]` moves
  every point of `ℤ[1/n]` within its residue class.  Along the level-`L` grid the increment of
  `f t - t` on one grid interval is `(n^j - 1) n^{-L}`, and `n - 1` divides `n^j - 1`.
* `exists_resEq_mem_Ioo`: every nonempty open interval meets every residue class of `ℤ[1/n]`.
-/

namespace GroupApproximation
namespace HigmanThompson

variable {m : ℕ}

theorem ResEq.add {x y x' y' : ℚ} (h : ResEq m x y) (h' : ResEq m x' y') :
    ResEq m (x + x') (y + y') := by
  obtain ⟨N₁, k₁, hk₁⟩ := h
  obtain ⟨N₂, k₂, hk₂⟩ := h'
  refine ⟨N₁ + N₂, k₁ * ((m : ℤ) + 2) ^ N₂ + k₂ * ((m : ℤ) + 2) ^ N₁, ?_⟩
  push_cast
  rw [pow_add]
  linear_combination ((m : ℚ) + 2) ^ N₂ * hk₁ + ((m : ℚ) + 2) ^ N₁ * hk₂

theorem mTwo_pow_sub_one_dvd (j : ℕ) : ∃ k : ℤ, ((m : ℤ) + 2) ^ j - 1 = ((m : ℤ) + 1) * k := by
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow ((m : ℤ) + 2) 1 j
  refine ⟨k, ?_⟩
  rw [one_pow] at hk
  have e : ((m : ℤ) + 2) - 1 = (m : ℤ) + 1 := by ring
  rw [e] at hk
  exact hk

/-- `n^j ε ≡ ε` for `ε ∈ ℤ[1/n]`. -/
theorem resEq_pow_mul (j : ℤ) {ε : ℚ} (hε : ∃ M, ε ∈ Grid (m + 2) M) :
    ResEq m (((m : ℚ) + 2) ^ j * ε) ε := by
  obtain ⟨M, e, he⟩ := hε
  push_cast at he
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    obtain ⟨k, hk⟩ := mTwo_pow_sub_one_dvd (m := m) a
    have hkQ : ((m : ℚ) + 2) ^ a - 1 = ((m : ℚ) + 1) * k := by exact_mod_cast hk
    refine ⟨M, k * e, ?_⟩
    rw [zpow_natCast]
    push_cast
    linear_combination (((m : ℚ) + 2) ^ a - 1) * he + (e : ℚ) * hkQ
  · obtain ⟨a, ha⟩ := Int.exists_eq_neg_ofNat hj.le
    subst ha
    obtain ⟨k, hk⟩ := mTwo_pow_sub_one_dvd (m := m) a
    have hkQ : ((m : ℚ) + 2) ^ a - 1 = ((m : ℚ) + 1) * k := by exact_mod_cast hk
    have hinv : (((m : ℚ) + 2) ^ a)⁻¹ * ((m : ℚ) + 2) ^ a = 1 :=
      inv_mul_cancel₀ (pow_ne_zero a mTwo_pos.ne')
    refine ⟨M + a, -(k * e), ?_⟩
    rw [zpow_neg, zpow_natCast, pow_add]
    push_cast
    linear_combination ε * ((m : ℚ) + 2) ^ M * hinv + (1 - ((m : ℚ) + 2) ^ a) * he -
      (e : ℚ) * hkQ

/-- **Residue invariance.**  A permutation in `PLGroup n (n^ℤ)` fixing `(-∞, 0]` pointwise moves
every point of `ℤ[1/n]` within its residue class modulo `(n-1) ℤ[1/n]`. -/
theorem resEq_apply_of_fix {f : Equiv.Perm ℚ} (hf : f ∈ PLGroup (m + 2) (powSlopes m))
    (hf0 : ∀ t : ℚ, t ≤ 0 → f t = t) {x : ℚ} {M : ℕ} (hx : x ∈ Grid (m + 2) M) :
    ResEq m (f x) x := by
  obtain ⟨-, ⟨N, B, hA⟩, -⟩ := hf
  have hA' := hA.mono_level (le_max_left N M)
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ (max N M) := pow_pos mTwo_pos _
  have hδgrid : ∃ M', (((m : ℚ) + 2) ^ (max N M))⁻¹ ∈ Grid (m + 2) M' :=
    ⟨max N M, mTwoPow_inv_mem_grid m (max N M)⟩
  have hstep : ∀ k : ℤ, gridPt (m + 2) (max N M) (k + 1) =
      gridPt (m + 2) (max N M) k + (((m : ℚ) + 2) ^ (max N M))⁻¹ := by
    intro k
    simp only [gridPt, hcast]
    push_cast
    ring
  have hnat : ∀ k : ℕ,
      ResEq m (f (gridPt (m + 2) (max N M) k)) (gridPt (m + 2) (max N M) k) := by
    intro k
    induction k with
    | zero =>
      have h0 : gridPt (m + 2) (max N M) ((0 : ℕ) : ℤ) = 0 := by simp [gridPt]
      rw [h0, hf0 0 le_rfl]
      exact ResEq.refl 0
    | succ k ih =>
      obtain ⟨s, ⟨j, rfl⟩, -, haff⟩ := hA'.slope (k : ℤ)
      have hk1 : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
      have hle : gridPt (m + 2) (max N M) (k : ℤ) ≤ gridPt (m + 2) (max N M) ((k : ℤ) + 1) := by
        rw [hstep]
        have := inv_pos.mpr hpos
        linarith
      have hval := haff (gridPt (m + 2) (max N M) ((k : ℤ) + 1)) hle le_rfl
      rw [hk1, hval, hstep]
      have e : f (gridPt (m + 2) (max N M) (k : ℤ)) + ((m : ℚ) + 2) ^ j *
          (gridPt (m + 2) (max N M) (k : ℤ) + (((m : ℚ) + 2) ^ (max N M))⁻¹ -
            gridPt (m + 2) (max N M) (k : ℤ)) =
          f (gridPt (m + 2) (max N M) (k : ℤ)) +
            ((m : ℚ) + 2) ^ j * (((m : ℚ) + 2) ^ (max N M))⁻¹ := by
        ring
      rw [e]
      exact ResEq.add ih (resEq_pow_mul j hδgrid)
  by_cases hx0 : x ≤ 0
  · rw [hf0 x hx0]
    exact ResEq.refl x
  obtain ⟨e, he⟩ := hx
  have hP : (((m + 2 : ℕ) : ℚ)) ^ (max N M) ≠ 0 := by
    rw [hcast]
    exact hpos.ne'
  obtain ⟨c, hc⟩ : ∃ c : ℤ, x * (((m + 2 : ℕ) : ℚ)) ^ (max N M) = c := by
    refine ⟨e * ((m : ℤ) + 2) ^ (max N M - M), ?_⟩
    have e1 : (((m + 2 : ℕ) : ℚ)) ^ (max N M) =
        (((m + 2 : ℕ) : ℚ)) ^ M * (((m + 2 : ℕ) : ℚ)) ^ (max N M - M) := by
      rw [← pow_add, Nat.add_sub_of_le (le_max_right N M)]
    rw [e1, ← mul_assoc, he]
    push_cast
    ring
  have hxc : x = gridPt (m + 2) (max N M) c := by
    unfold gridPt
    exact (eq_div_iff hP).mpr hc
  have hc0 : (0 : ℚ) ≤ (c : ℚ) := by
    rw [← hc]
    exact mul_nonneg (le_of_lt (not_le.mp hx0)) (pow_nonneg (Nat.cast_nonneg _) _)
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (by exact_mod_cast hc0 : (0 : ℤ) ≤ c)
  rw [hxc, ha]
  exact hnat a

/-- Every nonempty open interval meets every residue class of `ℤ[1/n]`. -/
theorem exists_resEq_mem_Ioo {x : ℚ} (hx : ∃ M, x ∈ Grid (m + 2) M) {u v : ℚ} (huv : u < v) :
    ∃ y : ℚ, u < y ∧ y < v ∧ ResEq m y x ∧ ∃ N, y ∈ Grid (m + 2) N := by
  obtain ⟨M, hxM⟩ := hx
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hm1 : (0 : ℚ) < (m : ℚ) + 1 := by linarith
  have hδ : 0 < (v - u) / ((m : ℚ) + 2) := div_pos (sub_pos.mpr huv) mTwo_pos
  obtain ⟨N, hN, hε⟩ := exists_level (m := m) M hδ
  have hεpos : (0 : ℚ) < (((m : ℚ) + 2) ^ N)⁻¹ := inv_pos.mpr (pow_pos mTwo_pos N)
  have hinv : (((m : ℚ) + 2) ^ N)⁻¹ * ((m : ℚ) + 2) ^ N = 1 :=
    inv_mul_cancel₀ (pow_ne_zero N mTwo_pos.ne')
  obtain ⟨w, hwdef⟩ : ∃ w : ℚ, w = ((m : ℚ) + 1) * (((m : ℚ) + 2) ^ N)⁻¹ := ⟨_, rfl⟩
  have hwpos : 0 < w := by
    rw [hwdef]
    exact mul_pos hm1 hεpos
  have hw : w < v - u := by
    have h1 : w ≤ ((m : ℚ) + 1) * ((v - u) / ((m : ℚ) + 2)) := by
      rw [hwdef]
      exact mul_le_mul_of_nonneg_left hε hm1.le
    have h2 : ((m : ℚ) + 1) * ((v - u) / ((m : ℚ) + 2)) < v - u := by
      rw [← mul_div_assoc, div_lt_iff₀ mTwo_pos]
      nlinarith [sub_pos.mpr huv]
    linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℤ, k = ⌊(u - x) / w⌋ + 1 := ⟨_, rfl⟩
  have hlow : u < x + w * k := by
    have h := Int.lt_floor_add_one ((u - x) / w)
    have hk : (u - x) / w < (k : ℚ) := by
      rw [hkdef]
      push_cast
      exact h
    rw [div_lt_iff₀ hwpos] at hk
    linarith
  have hhigh : x + w * k < v := by
    have h := Int.floor_le ((u - x) / w)
    have hk : (k : ℚ) - 1 ≤ (u - x) / w := by
      rw [hkdef]
      push_cast
      linarith
    rw [le_div_iff₀ hwpos] at hk
    nlinarith
  refine ⟨x + w * k, hlow, hhigh, ⟨N, k, ?_⟩, N, ?_⟩
  · rw [hwdef]
    linear_combination ((m : ℚ) + 1) * (k : ℚ) * hinv
  · refine grid_add (grid_mono hN hxM) ⟨((m : ℤ) + 1) * k, ?_⟩
    rw [hwdef]
    push_cast
    linear_combination ((m : ℚ) + 1) * (k : ℚ) * hinv

#audit_axioms GroupApproximation.HigmanThompson.resEq_apply_of_fix
#audit_axioms GroupApproximation.HigmanThompson.exists_resEq_mem_Ioo

end HigmanThompson
end GroupApproximation
