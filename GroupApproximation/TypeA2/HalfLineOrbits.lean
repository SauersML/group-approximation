import Mathlib.GroupTheory.GroupAction.Defs
import GroupApproximation.GroupTheory.HigmanThompson.CompactCore
import GroupApproximation.GroupTheory.HigmanThompson.PLMoves

/-!
# Geometric `F` on the positive dyadic rationals

`geoF 0` is the geometric Thompson group `F` of the half line: piecewise linear permutations of `ℚ`
over `(ℤ[1/2], 2^ℤ)` fixing `(-∞, 0]` and eventually an integer translation.  It preserves the set
`halfLineDyadics` of positive dyadic rationals.

* `geoF_zero_mapsTo`: `geoF 0` preserves `halfLineDyadics`.
* `exists_geoF_zero_move`: a PL move of `exists_move` at `n = 2`, with `0 ≤ α`, lies in `geoF 0`.
  At `n = 2` every pair of dyadic points has equal residue (`resEq_zero_of_grid`).
* `mem_orbit_one_geoF_zero`: `geoF 0` is transitive on `halfLineDyadics`.
* `geoF_zero_orbits_pairs`: `geoF 0` has three orbits on pairs, represented by `(1, 2)`, `(1, 1)`
  and `(2, 1)`.  For `x < y`, first push `y` above `x + 2` fixing `x`, then move `x` to `1` fixing
  `[x + 2, ∞)`, then move the image of `y` to `2` fixing `(-∞, 1]`.
-/

open MulAction

namespace GroupApproximation.TypeA2

open HigmanThompson

/-- The positive dyadic rationals `ℤ[1/2] ∩ (0, ∞)`. -/
def halfLineDyadics : Set ℚ := {t | 0 < t ∧ ∃ M, t ∈ Grid 2 M}

/-- `geoF 0` preserves the positive dyadic rationals. -/
theorem geoF_zero_mapsTo {g : Equiv.Perm ℚ} (hg : g ∈ geoF 0) {x : ℚ} (hx : x ∈ halfLineDyadics) :
    g x ∈ halfLineDyadics := by
  obtain ⟨⟨hmono, ⟨N, B, hGA⟩, -⟩, hfix, -⟩ := hg
  obtain ⟨hx0, M, hM⟩ := hx
  refine ⟨?_, B + max M N, hGA.mapsGrid hM⟩
  have h := hmono hx0
  rwa [hfix 0 le_rfl] at h

/-- At `n = 2` all dyadic points have the same residue. -/
theorem resEq_zero_of_grid {x y : ℚ} {Mx My : ℕ} (hx : x ∈ Grid 2 Mx) (hy : y ∈ Grid 2 My) :
    ResEq 0 x y := by
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  refine ⟨Mx + My, kx * 2 ^ My - ky * 2 ^ Mx, ?_⟩
  push_cast at hkx hky ⊢
  linear_combination (2 : ℚ) ^ My * hkx - (2 : ℚ) ^ Mx * hky

/-- A move of geometric `F` at `n = 2`: moving a dyadic `x` to a dyadic `y` inside `(α, β)`, with
`0 ≤ α`. -/
theorem exists_geoF_zero_move {α β x y : ℚ} {Mα Mβ Mx My : ℕ} (hα : α ∈ Grid 2 Mα)
    (hβ : β ∈ Grid 2 Mβ) (hx : x ∈ Grid 2 Mx) (hy : y ∈ Grid 2 My) (hα0 : 0 ≤ α) (hαx : α < x)
    (hαy : α < y) (hxβ : x < β) (hyβ : y < β) :
    ∃ g ∈ geoF 0, (∀ u, u ≤ α → g u = u) ∧ (∀ u, β ≤ u → g u = u) ∧ g x = y := by
  obtain ⟨g, hg, hlow, hhigh, hgxy⟩ :=
    exists_move 0 ⟨Mα, hα⟩ ⟨Mβ, hβ⟩ (resEq_zero_of_grid hx hy) hαx hαy hxβ hyβ
  refine ⟨g, ⟨hg, fun t ht => hlow t (ht.trans hα0), ⌈β⌉₊, 0, fun t ht => ?_⟩, hlow, hhigh, hgxy⟩
  rw [hhigh t ((Nat.le_ceil β).trans ht), Int.cast_zero, add_zero]

/-- Every positive dyadic point moves to `1`, by an element fixing `[x + 2, ∞)`. -/
theorem exists_geoF_zero_one {x : ℚ} (hx : x ∈ halfLineDyadics) :
    ∃ g ∈ geoF 0, (∀ u, x + 2 ≤ u → g u = u) ∧ g x = 1 := by
  obtain ⟨hx0, Mx, hMx⟩ := hx
  obtain ⟨α, hα0, hαx, Mα, hα⟩ := exists_grid_mem_Ioo (m := 0) (lt_min hx0 one_pos)
  obtain ⟨β, hβ1, hβ2, Mβ, hβ⟩ := exists_grid_mem_Ioo (m := 0) (show x + 1 < x + 2 by linarith)
  obtain ⟨g, hg, -, hhigh, hgx⟩ := exists_geoF_zero_move hα hβ hMx (one_mem_grid_mTwo 0 0)
    hα0.le (lt_of_lt_of_le hαx (min_le_left _ _)) (lt_of_lt_of_le hαx (min_le_right _ _))
    (by linarith) (by linarith)
  exact ⟨g, hg, fun u hu => hhigh u (by linarith), hgx⟩

/-- An increasing pair of positive dyadic points moves to `(1, 2)`. -/
theorem exists_geoF_zero_one_two {x y : ℚ} (hx : x ∈ halfLineDyadics) (hy : y ∈ halfLineDyadics)
    (hxy : x < y) : ∃ g ∈ geoF 0, g x = 1 ∧ g y = 2 := by
  obtain ⟨hx0, Mx, hMx⟩ := hx
  obtain ⟨hy0, My, hMy⟩ := hy
  obtain ⟨α₁, hα₁x, hα₁y, Mα₁, hα₁⟩ := exists_grid_mem_Ioo (m := 0) hxy
  obtain ⟨y₁, hy₁l, -, My₁, hMy₁⟩ :=
    exists_grid_mem_Ioo (m := 0) (show x + y + 2 < x + y + 3 by linarith)
  obtain ⟨β₁, hβ₁l, -, Mβ₁, hβ₁⟩ := exists_grid_mem_Ioo (m := 0) (show y₁ < y₁ + 1 by linarith)
  obtain ⟨g₁, hg₁, hg₁low, -, hg₁y⟩ := exists_geoF_zero_move hα₁ hβ₁ hMy hMy₁ (by linarith) hα₁y
    (by linarith) (by linarith) hβ₁l
  obtain ⟨g₂, hg₂, hg₂high, hg₂x⟩ := exists_geoF_zero_one ⟨hx0, Mx, hMx⟩
  obtain ⟨α₃, hα₃l, hα₃r, Mα₃, hα₃⟩ := exists_grid_mem_Ioo (m := 0) (show (1 : ℚ) < 2 by norm_num)
  obtain ⟨β₃, hβ₃l, -, Mβ₃, hβ₃⟩ := exists_grid_mem_Ioo (m := 0) (show y₁ + 1 < y₁ + 2 by linarith)
  have h2 : (2 : ℚ) ∈ Grid 2 0 := by simpa using int_mem_grid (m := 2) 0 2
  obtain ⟨g₃, hg₃, hg₃low, -, hg₃y⟩ := exists_geoF_zero_move hα₃ hβ₃ hMy₁ h2 (by linarith)
    (by linarith) hα₃r (by linarith) (by linarith)
  refine ⟨g₃ * g₂ * g₁, mul_mem (mul_mem hg₃ hg₂) hg₁, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg₁low x hα₁x.le, hg₂x, hg₃low 1 hα₃l.le]
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg₁y, hg₂high y₁ (by linarith), hg₃y]

/-- `geoF 0` is transitive on the positive dyadic rationals. -/
theorem mem_orbit_one_geoF_zero {x : ℚ} (hx : x ∈ halfLineDyadics) :
    x ∈ orbit (geoF 0) (1 : ℚ) := by
  obtain ⟨g, hg, -, h1⟩ := exists_geoF_zero_one hx
  exact mem_orbit_iff.mpr ⟨⟨g⁻¹, inv_mem hg⟩, perm_inv_eq_of_apply_eq h1⟩

/-- **Three orbits on pairs.**  Every pair of positive dyadic points is the image of `(1, 2)`,
`(1, 1)` or `(2, 1)` under `geoF 0`. -/
theorem geoF_zero_orbits_pairs :
    ∃ F : Finset (ℚ × ℚ), ∀ x ∈ halfLineDyadics, ∀ y ∈ halfLineDyadics,
      ∃ f ∈ F, ∃ g ∈ geoF 0, g f.1 = x ∧ g f.2 = y := by
  classical
  refine ⟨{(1, 2), (1, 1), (2, 1)}, fun x hx y hy => ?_⟩
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨g, hg, h1, h2⟩ := exists_geoF_zero_one_two hx hy hxy
    exact ⟨(1, 2), by simp, g⁻¹, inv_mem hg, perm_inv_eq_of_apply_eq h1,
      perm_inv_eq_of_apply_eq h2⟩
  · obtain ⟨g, hg, -, h1⟩ := exists_geoF_zero_one hx
    exact ⟨(1, 1), by simp, g⁻¹, inv_mem hg, perm_inv_eq_of_apply_eq h1,
      perm_inv_eq_of_apply_eq h1⟩
  · obtain ⟨g, hg, h1, h2⟩ := exists_geoF_zero_one_two hy hx hxy
    exact ⟨(2, 1), by simp, g⁻¹, inv_mem hg, perm_inv_eq_of_apply_eq h2,
      perm_inv_eq_of_apply_eq h1⟩

end GroupApproximation.TypeA2
