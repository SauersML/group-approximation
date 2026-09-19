import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.CohomologySphere

/-!
# The Künneth map for a sphere factor, and the half of its injectivity that a slice sees

For a space `Y` and `n ≥ 1` the Künneth map with a sphere factor is

```text
H^{n+m}(Y) ⊕ H^m(Y) → H^{n+m}(Y × S^n; F₂),
  (u, v) ↦ pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v.
```

Restricting along a slice `y ↦ (y, p)` retracts `pr_Y^*` and **kills** the sphere
class, because a slice factors the sphere projection through a constant map and
`H^n(pt; F₂) = 0` for `n ≥ 1`.  So a slice detects the first component exactly:
if the Künneth map sends `(u, v)` to zero then `u = 0`.

That is one of the two halves of the injectivity statement `tx_inj` that lane
`cc-wu`'s `ParityData` consumes.  The other half, `(pr_S^* σ_n) ⌣ pr_Y^* v = 0 →
v = 0`, is **not** here: it needs the `H^*(X)`-linearity of the Mayer–Vietoris
connecting map for a globally defined class, which is a cochain-level statement.
See the module footer.

## Main declarations

* `knPrY`, `knPrS`, `knSlice` — the two projections and a slice.
* `pull_knSlice_knPrY` — a slice retracts the projection, so `pr_Y^*` is a split
  injection in every degree.
* `knSigma` — the mod-2 fundamental class of the sphere factor, pulled back.
* `pull_knSlice_knSigma` — a slice kills it.
* `kunneth_fst_eq_zero` — the first component of the Künneth map is detected by a
  slice.
* `prodSwapEquiv` — the two orientations `Y × S^n` and `S^n × Y` agree.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

/-! ## 1. The projections and a slice -/

/-- The projection of `Y × S^n` onto `Y`. -/
abbrev knPrY : TopCat.of (Y × Sphere n) ⟶ TopCat.of Y := cmap ContinuousMap.fst

/-- The projection of `Y × S^n` onto the sphere factor. -/
abbrev knPrS : TopCat.of (Y × Sphere n) ⟶ TopCat.of (Sphere n) := cmap ContinuousMap.snd

/-- The slice `y ↦ (y, p)` of `Y × S^n`. -/
def knSlice (p : Sphere n) : TopCat.of Y ⟶ TopCat.of (Y × Sphere n) :=
  cmap (ContinuousMap.prodMk (ContinuousMap.id Y) (ContinuousMap.const Y p))

theorem knSlice_comp_prY (p : Sphere n) : knSlice Y n p ≫ knPrY Y n = 𝟙 (TopCat.of Y) := rfl

theorem knSlice_comp_prS (p : Sphere n) :
    knSlice Y n p ≫ knPrS Y n = cmap (ContinuousMap.const Y p) := rfl

/-- **A slice retracts the projection.**  So `pr_Y^*` is a split injection in every
degree. -/
@[simp] theorem pull_knSlice_knPrY (p : Sphere n) (k : ℕ) (u : Hmod2 (TopCat.of Y) k) :
    pull (knSlice Y n p) k (pull (knPrY Y n) k u) = u := by
  rw [← pull_comp, knSlice_comp_prY, pull_id]

theorem pull_knPrY_injective (p : Sphere n) (k : ℕ) :
    Function.Injective (pull (knPrY Y n) k) := by
  intro u u' h
  have h2 := congrArg (pull (knSlice Y n p) k) h
  rwa [pull_knSlice_knPrY, pull_knSlice_knPrY] at h2

/-! ## 2. A constant map kills positive degrees -/

/-- A constant map factors through a point, so it kills every class of positive
degree. -/
theorem pull_const_eq_zero {Z : Type} [TopologicalSpace Z] (p : Z) (k : ℕ) (hk : 1 ≤ k)
    (a : Hmod2 (TopCat.of Z) k) :
    pull (cmap (ContinuousMap.const Y p)) k a = 0 := by
  have hfac : (cmap (ContinuousMap.const Y p) : TopCat.of Y ⟶ TopCat.of Z)
      = cmap (ContinuousMap.const Y (() : Unit)) ≫ cmap (ContinuousMap.const Unit p) := rfl
  have hz : pull (cmap (ContinuousMap.const Unit p)) k a = 0 := by
    have h := cohomology_unit_isZero k hk
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h.elim _ 0
  rw [hfac, pull_comp, hz, pull_zero]

/-! ## 3. The sphere class and the slice -/

/-- The mod-2 fundamental class of the sphere factor, pulled back to the product. -/
def knSigma (hn : 1 ≤ n) : Hmod2 (TopCat.of (Y × Sphere n)) n :=
  pull (knPrS Y n) n (sphereTopClass n hn)

/-- **A slice kills the sphere class.** -/
@[simp] theorem pull_knSlice_knSigma (hn : 1 ≤ n) (p : Sphere n) :
    pull (knSlice Y n p) n (knSigma Y n hn) = 0 := by
  rw [knSigma, ← pull_comp, knSlice_comp_prS]
  exact pull_const_eq_zero Y p n hn _

/-! ## 4. The first component of the Künneth map -/

/-- **A slice detects the first component of the Künneth map.**  If
`pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v = 0` then `u = 0`. -/
theorem kunneth_fst_eq_zero (hn : 1 ≤ n) (p : Sphere n) (m : ℕ)
    (u : Hmod2 (TopCat.of Y) (n + m)) (v : Hmod2 (TopCat.of Y) m)
    (h : pull (knPrY Y n) (n + m) u + cup (knSigma Y n hn) (pull (knPrY Y n) m v) = 0) :
    u = 0 := by
  have h2 := congrArg (pull (knSlice Y n p) (n + m)) h
  rw [pull_add, pull_cup, pull_knSlice_knSigma, zero_cup, add_zero, pull_knSlice_knPrY,
    pull_zero] at h2
  exact h2

/-! ## 5. The two orientations of the product -/

/-- The cohomology of `B × A` and of `A × B` agree, by the swap homeomorphism. -/
def prodSwapEquiv (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (k : ℕ) :
    Hmod2 (TopCat.of (B × A)) k ≃ₗ[ZMod 2] Hmod2 (TopCat.of (A × B)) k :=
  pullEquivOfHomeomorph (Homeomorph.prodComm A B) k

end

end GroupApproximation.CharClass

/-!
## What is missing, and why

The other half of the Künneth injectivity,

```text
(pr_S^* σ_n) ⌣ pr_Y^* v = 0   →   v = 0,
```

cannot be reached from a slice: a slice kills the sphere class, so it kills the
whole term.  The only route is the Mayer–Vietoris sequence of the hemisphere
cover of the sphere factor, in which `(pr_S^* σ_n) ⌣ pr_Y^* v` is the image under
the connecting map of `pr_Y^* v` restricted to the equatorial band.  Identifying
it that way is exactly the `H^*(X)`-linearity of the connecting map for a
globally defined class,

```text
δ (a ⌣ b|_{U ⊓ V}) = δ a ⌣ b,
```

which is a cochain-level statement about the explicit "lift, differentiate,
descend" description of `δ` (Mathlib's `ShortComplex.ShortExact.δ_eq` gives that
description).  Until it exists, `tx_inj` of `cc-wu`'s `ParityData` is out of
reach, and no amount of group-level Künneth substitutes for it.
-/
