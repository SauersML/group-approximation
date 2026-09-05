import Mathlib

/-!
# The zero locus of the mapping-torus section

Lane `found-euler-class`, campaign target 3 (STW Problem LIX).

The counterexample manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
proof of Lemma 2) forms the section

```text
S (x, y, t) = ((1 - t) • e₃ + t • x,  χ t • σ y)                        (2.10)
```

of `V = 1³ ⊕ H` over `S⁵ × Y × [0,1]`, where `χ : [0,1] → [0,1]` vanishes near both
endpoints and equals `1` near `1/2`, and asserts

> Its zeros occur exactly at `t = 1/2`, `x = -e₃`, `σ y = 0`.

This file proves that assertion.  It is pure normed-space algebra: no bundle, no
gluing, no smoothness, no orientation, and in particular it is valid verbatim for the
*topological* bundle of (2.9), which is the case the manuscript has to handle because
the automorphism `g` is only assumed continuous.

Composition with the rest of the Euler half:

* the zero in the `S⁵ × [0,1]` directions is the single point `(-e₃, 1/2)`
  (`seam_component_eq_zero_iff` below), and at it the derivative is the linear
  isomorphism `GroupApproximation.AlgTop.eulerLocalModelEquiv`
  (`AlgTop/EulerLocalModel.lean`);
* the zeros in the `Y` directions are the zeros of `σ`, and for the campaign's explicit
  `σ` there is exactly one of them
  (`GroupApproximation.AlgTop.dualTautSection_eq_zero_iff`,
  `AlgTop/CPTautologicalSection.lean`).

## Main results

* `seam_component_eq_zero_iff` — `(1-t) • v + t • x = 0` for unit vectors `v`, `x` and
  `t ∈ [0,1]` holds **iff** `t = 1/2` and `x = -v`.
* `mappingTorusSection_eq_zero_iff` — the full zero locus of (2.10).
* `mappingTorusSection_ne_zero_of_ne_half` — the section is nonvanishing off `t = 1/2`,
  which is the manuscript's "nonvanishing near the seam": the seam of the gluing sits at
  `t ∈ {0, 1}` and the only zero has `t = 1/2`, so the gluing is invisible to the zero
  set and the local-index count runs on the topological bundle unchanged.
-/

noncomputable section

namespace GroupApproximation.AlgTop

/-! ## 1. The sphere-and-interval component -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The zero of the `ℂ³`-component.**  For unit vectors `v` and `x` and a parameter
`t ∈ [0,1]`, the straight path `(1-t) • v + t • x` from `v` to `x` passes through the
origin exactly when `t = 1/2` and `x` is antipodal to `v`.

In the manuscript `v = e₃` and `x` ranges over `S⁵`; this is the assertion that the
`ℂ³`-component of (2.10) vanishes exactly at `t = 1/2`, `x = -e₃`. -/
theorem seam_component_eq_zero_iff {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • v + t • x = 0 ↔ (t = 1 / 2 ∧ x = -v) := by
  constructor
  · intro h
    -- Compare norms across `(1-t) • v = -(t • x)`.
    have hneg : (1 - t) • v = -(t • x) := by
      rw [← sub_eq_zero, sub_neg_eq_add]
      exact h
    have hnorm : ‖(1 - t) • v‖ = ‖t • x‖ := by
      rw [hneg, norm_neg]
    have hL : ‖(1 - t) • v‖ = 1 - t := by
      rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_nonneg (by linarith)]
    have hR : ‖t • x‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, hx, mul_one, abs_of_nonneg ht0]
    have ht : t = 1 / 2 := by
      rw [hL, hR] at hnorm
      linarith
    refine ⟨ht, ?_⟩
    -- With `t = 1/2` the relation reads `(1/2) • (v + x) = 0`.
    subst ht
    have h2 : ((1 : ℝ) / 2) • (v + x) = 0 := by
      rw [smul_add]
      norm_num at h ⊢
      exact h
    have hne : ((1 : ℝ) / 2) ≠ 0 := by norm_num
    have h3 : v + x = 0 := (smul_eq_zero.mp h2).resolve_left hne
    have h4 : x = -v := by
      have := eq_neg_of_add_eq_zero_right h3
      exact this
    exact h4
  · rintro ⟨ht, hxv⟩
    subst ht
    subst hxv
    norm_num

/-! ## 2. The full section -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The zero locus of (2.10).**  With `χ (1/2) = 1`, the section
`((1-t) • v + t • x, χ t • w)` vanishes exactly at `t = 1/2`, `x = -v`, `w = 0`.

`w` stands for `σ y`; the statement is pointwise in `y`, so the zero set of the section
is `{(-v, y, 1/2) : σ y = 0}`, which is the manuscript's description. -/
theorem mappingTorusSection_eq_zero_iff {χ : ℝ → ℝ} (hχ : χ (1 / 2) = 1) {v x : E} {w : F}
    (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • v + t • x = 0 ∧ χ t • w = 0) ↔ (t = 1 / 2 ∧ x = -v ∧ w = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨ht, hxv⟩ := (seam_component_eq_zero_iff hv hx ht0 ht1).mp h1
    refine ⟨ht, hxv, ?_⟩
    rw [ht, hχ, one_smul] at h2
    exact h2
  · rintro ⟨ht, hxv, hw⟩
    refine ⟨(seam_component_eq_zero_iff hv hx ht0 ht1).mpr ⟨ht, hxv⟩, ?_⟩
    rw [hw, smul_zero]

/-- **Nonvanishing off `t = 1/2`,** in particular near the seam `t ∈ {0, 1}` of the
gluing (2.9).  This is the step the manuscript needs in order to run the local-index
count on a *topological* bundle: the gluing is invisible to the zero set. -/
theorem mappingTorusSection_ne_zero_of_ne_half {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht : t ≠ 1 / 2) :
    (1 - t) • v + t • x ≠ 0 := by
  intro h
  exact ht ((seam_component_eq_zero_iff hv hx ht0 ht1).mp h).1

/-- The endpoint values of (2.10): at `t = 0` the section is `(v, 0)` (the manuscript's
`e`), at `t = 1` it is `(x, 0)` (the manuscript's `s`), provided `χ` vanishes at both
endpoints.  This is the compatibility that makes the section descend to the mapping
torus of an automorphism carrying `e` to `s`. -/
theorem mappingTorusSection_endpoints {χ : ℝ → ℝ} (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 0)
    (v x : E) (w : F) :
    ((1 - (0 : ℝ)) • v + (0 : ℝ) • x, χ 0 • w) = (v, (0 : F)) ∧
      ((1 - (1 : ℝ)) • v + (1 : ℝ) • x, χ 1 • w) = (x, (0 : F)) := by
  refine ⟨?_, ?_⟩
  · rw [hχ0]
    simp
  · rw [hχ1]
    simp

end GroupApproximation.AlgTop
