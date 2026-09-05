import GroupApproximation.AlgTop.CPTautologicalSection
import GroupApproximation.AlgTop.MappingTorusSectionZeros

/-!
# The manuscript's mapping-torus section has exactly one zero

Lane `found-euler-class`, campaign target 3 (STW Problem LIX).

This file assembles the two halves proved in `AlgTop/MappingTorusSectionZeros.lean` and
`AlgTop/CPTautologicalSection.lean` into the statement the parity argument of the
counterexample manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
proof of Lemma 2) actually needs:

> the section (2.10) of `W_g` has isolated zeros whose count is `1`.

The manuscript reaches the count `±1` through the Chern number
`|⟨c_m(H), [Y]⟩| = 1` of (2.1).  Here the count is instead *exhibited*: over
`Y = ∏ⱼ ℂP^{dⱼ}` with `H = ⊕ⱼ (L_j*)^{⊕dⱼ}` built from the **dual** tautological
lines, the coordinate-functional section has exactly one zero, namely the tuple of
base points, and combining with the `S⁵ × [0,1]` factor the whole section has exactly
one zero, namely `(-e₃, (basePoint)ⱼ, 1/2)`.

Nothing below uses a characteristic class, a cohomology group, an orientation, a
fundamental class, or any smoothness: it is linear algebra about rank-one projections
plus a norm comparison.  What is *not* proved here — and is not provable without a
Thom/Euler class — is the passage from "exactly one zero" to "the Euler number is odd".
That interface is the campaign's remaining topological wall; see the lane report.

## Main results

* `productDualTautSection_eq_zero_iff` — over the product `∏ⱼ ℂP^{dⱼ}`, the section of
  `H` vanishes exactly at the tuple of base points.
* `manuscriptSection_eq_zero_iff` — the zero locus of (2.10) is the single point
  `(-e₃, (basePoint)ⱼ, 1/2)`.
* `manuscriptSection_zero_unique` — any two zeros coincide, in all three coordinates.
-/

noncomputable section

namespace GroupApproximation.AlgTop

/-! ## 1. The section of `H` over a product of projective spaces -/

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The manuscript's section `σ` of `H = ⊕ⱼ (L_j*)^{⊕dⱼ}` over `Y = ∏ⱼ ℂP^{dⱼ}`: on
the `j`-th factor it is the coordinate-functional section `dualTautSection`. -/
def productDualTautSection (y : ∀ j, CP (dd j)) :
    ∀ j : Fin ℓ, Fin (dd j) → Fin (dd j + 1) → ℂ :=
  fun j => dualTautSection (y j)

@[simp]
theorem productDualTautSection_apply (y : ∀ j, CP (dd j)) (j : Fin ℓ) (i : Fin (dd j))
    (k : Fin (dd j + 1)) :
    productDualTautSection y j i k = (y j).mat i.succ k := rfl

/-- **The section of `H` has exactly one zero.**  Over `Y = ∏ⱼ ℂP^{dⱼ}` it vanishes
exactly at the tuple of base points.  This is the manuscript's `|⟨c_m(H), [Y]⟩| = 1`
of (2.1), proved as linear algebra rather than as a Chern-number computation. -/
theorem productDualTautSection_eq_zero_iff (y : ∀ j, CP (dd j)) :
    (∀ j i k, productDualTautSection y j i k = 0) ↔ y = fun j => CP.basePoint (dd j) := by
  constructor
  · intro h
    funext j
    exact (dualTautSection_eq_zero_iff (y j)).mp (fun i k => h j i k)
  · intro h j i k
    have hj : y j = CP.basePoint (dd j) := congrFun h j
    exact (dualTautSection_eq_zero_iff (y j)).mpr hj i k

/-! ## 2. The whole section of `W_g` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The zero locus of the manuscript's section (2.10).**

`((1-t) • e₃ + t • x, χ t • σ y)` vanishes exactly at `t = 1/2`, `x = -e₃` and
`y` the tuple of base points.  So the section has exactly one zero — an odd number,
which is the whole content the parity contradiction needs from this side. -/
theorem manuscriptSection_eq_zero_iff {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    {χ : ℝ → ℝ} (hχ : χ (1 / 2) = 1) (y : ∀ j, CP (dd j)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • v + t • x = 0 ∧
        ∀ j i k, ((χ t : ℝ) : ℂ) * productDualTautSection y j i k = 0)
      ↔ (t = 1 / 2 ∧ x = -v ∧ y = fun j => CP.basePoint (dd j)) := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨ht, hxv⟩ := (seam_component_eq_zero_iff hv hx ht0 ht1).mp h1
    refine ⟨ht, hxv, ?_⟩
    refine (productDualTautSection_eq_zero_iff y).mp (fun j i k => ?_)
    have hk := h2 j i k
    rw [ht, hχ] at hk
    simpa using hk
  · rintro ⟨ht, hxv, hy⟩
    refine ⟨(seam_component_eq_zero_iff hv hx ht0 ht1).mpr ⟨ht, hxv⟩, fun j i k => ?_⟩
    have hz : productDualTautSection y j i k = 0 :=
      (productDualTautSection_eq_zero_iff y).mpr hy j i k
    rw [hz, mul_zero]

/-- **Uniqueness of the zero.**  Any two zeros of (2.10) agree in all three
coordinates.  Together with `manuscriptSection_eq_zero_iff` this is the statement
"the section has exactly one zero", with no counting measure and no orientation. -/
theorem manuscriptSection_zero_unique {v x x' : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    (hx' : ‖x'‖ = 1) {χ : ℝ → ℝ} (hχ : χ (1 / 2) = 1) (y y' : ∀ j, CP (dd j))
    {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1)
    (h : (1 - t) • v + t • x = 0 ∧
        ∀ j i k, ((χ t : ℝ) : ℂ) * productDualTautSection y j i k = 0)
    (h' : (1 - t') • v + t' • x' = 0 ∧
        ∀ j i k, ((χ t' : ℝ) : ℂ) * productDualTautSection y' j i k = 0) :
    x = x' ∧ y = y' ∧ t = t' := by
  obtain ⟨ht, hxv, hy⟩ := (manuscriptSection_eq_zero_iff hv hx hχ y ht0 ht1).mp h
  obtain ⟨ht', hxv', hy'⟩ := (manuscriptSection_eq_zero_iff hv hx' hχ y' ht0' ht1').mp h'
  exact ⟨by rw [hxv, hxv'], by rw [hy, hy'], by rw [ht, ht']⟩

/-- The zero of (2.10) really is attained: the displayed point is a zero.  (Together
with `manuscriptSection_zero_unique`, the zero count is exactly one, not zero.) -/
theorem manuscriptSection_zero_exists {v : E} (hv : ‖v‖ = 1) {χ : ℝ → ℝ}
    (hχ : χ (1 / 2) = 1) :
    ((1 - (1 / 2 : ℝ)) • v + (1 / 2 : ℝ) • (-v) = 0 ∧
      ∀ j i k, ((χ (1 / 2 : ℝ) : ℝ) : ℂ) *
        productDualTautSection (dd := dd) (fun j => CP.basePoint (dd j)) j i k = 0) := by
  have hx : ‖(-v : E)‖ = 1 := by simpa using hv
  exact (manuscriptSection_eq_zero_iff (v := v) (x := -v) (t := 1 / 2) hv hx hχ
    (fun j => CP.basePoint (dd j)) (by norm_num) (by norm_num)).mpr ⟨rfl, rfl, rfl⟩

end GroupApproximation.AlgTop
