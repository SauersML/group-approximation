import Mathlib

/-!
# The unique zero of the mapping-torus section along the sphere direction

Lane `lix-obstruction`, campaign target 3 (STW Problem LIX).

The proof of Lemma 2 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
uses the section

```text
S (x, y, t) = ((1 - t) • e₃ + t • x, χ t • σ y)
```

of `V = 1³ ⊕ H` over `S⁵ × Y × [0,1]`, and asserts that "its zeros occur exactly at
`t = 1/2`, `x = -e₃`, `σ y = 0`".  This file proves the sphere half of that
assertion, in the generality in which it is used: `v` and `x` unit vectors of a real
normed space (`ℂ³` with its scalars restricted to `ℝ`), and `t` a real number.

The statement proved is sharper than the bare zero set, and the sharp form is what
shows the section is nonvanishing near the gluing seam: the norm of the segment is
bounded below by `| |1 - t| - |t| |`, which on `[0,1]` is `|1 - 2t|`.  So the section
is nonzero for every `t ≠ 1/2`, in particular on a neighbourhood of `t ∈ {0, 1}`, and
the mapping torus is glued along a region where the section does not vanish.

Everything here is a norm computation: no bundle, no smoothness, no orientation.

## Main results

* `abs_sub_abs_le_norm_segment` — the lower bound `| |1-t| - |t| | ≤ ‖(1-t) • v + t • x‖`.
* `norm_segment_ge_abs_one_sub_two_mul` — on `[0,1]` the bound reads `|1 - 2t|`.
* `segment_eq_zero_iff` — the segment vanishes iff `t = 1/2` and `x = -v`.
* `segment_ne_zero_of_ne_half` — the contrapositive, in the form used near the seam.
* `segment_pair_eq_zero_iff` — the zero set of the full pair `S`.
-/

namespace GroupApproximation
namespace STW59

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lower bound on the norm of the segment between two unit vectors, with the
weights `1 - t` and `t`.  No constraint on `t`. -/
theorem abs_sub_abs_le_norm_segment {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (t : ℝ) :
    ||1 - t| - |t|| ≤ ‖(1 - t) • v + t • x‖ := by
  have h := abs_norm_sub_norm_le ((1 - t) • v) (-(t • x))
  rw [sub_neg_eq_add, norm_neg, norm_smul, norm_smul, hv, hx, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- On the parameter interval `[0,1]` the lower bound is `|1 - 2t|`, so the segment is
nonzero away from the midpoint. -/
theorem norm_segment_ge_abs_one_sub_two_mul {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    |1 - 2 * t| ≤ ‖(1 - t) • v + t • x‖ := by
  have h := abs_sub_abs_le_norm_segment hv hx t
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht₀,
    show (1 : ℝ) - t - t = 1 - 2 * t from by ring] at h
  exact h

/-- **The segment between two unit vectors vanishes exactly at the midpoint of an
antipodal pair.**  This is the manuscript's "`t = 1/2`, `x = -e₃`". -/
theorem segment_eq_zero_iff {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (t : ℝ) :
    (1 - t) • v + t • x = 0 ↔ t = 1 / 2 ∧ x = -v := by
  constructor
  · intro h
    have hnorm : ||1 - t| - |t|| ≤ 0 := by
      have h' := abs_sub_abs_le_norm_segment hv hx t
      rwa [h, norm_zero] at h'
    have hz : |1 - t| - |t| = 0 := abs_eq_zero.mp (le_antisymm hnorm (abs_nonneg _))
    have habs : |1 - t| = |t| := sub_eq_zero.mp hz
    have ht : t = 1 / 2 := by
      rcases abs_eq_abs.mp habs with h' | h'
      · linarith
      · exfalso; linarith
    subst ht
    refine ⟨rfl, ?_⟩
    have h2 : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • x = 0 := by
      rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num] at h
    have h3 : (1 / 2 : ℝ) • (v + x) = 0 := by rw [smul_add]; exact h2
    have hvx : v + x = 0 := by
      have h4 : (2 : ℝ) • ((1 / 2 : ℝ) • (v + x)) = (2 : ℝ) • (0 : E) := by rw [h3]
      rwa [smul_smul, smul_zero, show (2 : ℝ) * (1 / 2) = 1 from by norm_num,
        one_smul] at h4
    have h5 : x = -v + (v + x) := by abel
    rwa [hvx, add_zero] at h5
  · rintro ⟨rfl, rfl⟩
    module

/-- The form used near the gluing seam: away from the midpoint the segment is nonzero,
whatever the two unit vectors are. -/
theorem segment_ne_zero_of_ne_half {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) {t : ℝ}
    (ht : t ≠ 1 / 2) : (1 - t) • v + t • x ≠ 0 := fun h =>
  ht ((segment_eq_zero_iff hv hx t).mp h).1

/-- The zero set of the pair, which is the shape in which the manuscript's section `S`
is used: the pair vanishes iff `t = 1/2`, `x = -v`, and the second component vanishes.
For `S` the second component is `χ t • σ y`, so the zero set is
`{t = 1/2} × {x = -e₃} × {σ y = 0}`, as asserted in the manuscript. -/
theorem segment_pair_eq_zero_iff {F : Type*} [NormedAddCommGroup F] {v x : E} (c : F)
    (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (t : ℝ) :
    ((1 - t) • v + t • x, c) = ((0 : E), (0 : F)) ↔ t = 1 / 2 ∧ x = -v ∧ c = 0 := by
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨ht, hxv⟩ := (segment_eq_zero_iff hv hx t).mp h₁
    exact ⟨ht, hxv, h₂⟩
  · rintro ⟨ht, hxv, hc⟩
    exact ⟨(segment_eq_zero_iff hv hx t).mpr ⟨ht, hxv⟩, hc⟩

end STW59
end GroupApproximation
