import GroupApproximation.CharClass.CohomologyKunnethBand
import GroupApproximation.CharClass.CohomologyDeltaNatural

/-!
# The Künneth induction step

The statement `σ_n ⌣ pr_Y^* v = 0 → v = 0` is not the right inductive predicate.
The one that propagates is

```text
KnGen n t : ∀ Y m (v : H^m(Y)) (c : H^{n+m}(Y)),
    pr_S^* t ⌣ pr_Y^* v = pr_Y^* c → v = 0
```

For `n ≥ 1` the two are equivalent, because a slice `y ↦ (y, p)` kills
`pr_S^* t` and sends `pr_Y^* c` to `c`, so `c = 0` for free.  At `n = 0` the
`KnGen` form is genuinely stronger, and supplying it there is the whole content
of the base case.

The step itself is the Mayer–Vietoris argument.  With `t₁` the suspension of
`t₀`, naturality of `δ` along the sphere projection turns `pr_S^* t₁` into `δ τ`,
δ-linearity turns `δ τ ⌣ pr^* v` into `δ (τ ⌣ pr^* v)`, exactness makes
`τ ⌣ pr^* v` a sum of restrictions from the two hemispheres, and both
hemispheres are `Y` through the projection, so that sum is a pullback from `Y`.
Transporting along the band equivalence is exactly the hypothesis of `KnGen n t₀`.

## Main declarations

* `KnHemi.sphereNext` — the suspension of a sphere class.
* `KnHemi.KnGen`, `KnHemi.knGen_of_injective`.
* `KnHemi.injective_sphereNext` — the step.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-! ## 0. Two small facts -/

theorem cohCast_zero {X : TopCat.{0}} {m m' : ℕ} (h : m = m') :
    cohCast h (0 : Hmod2 X m) = 0 := by
  subst h
  rfl

theorem pull_sInclusion_knPrY (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (S : Set ↥(prodTop Y n)) (k : ℕ) (v : Hmod2 (TopCat.of Y) k) :
    pull (sInclusion S) k (pull (knPrY Y (n + 1)) k v) = pull (prSub Y n S) k v := by
  rw [← pull_comp, sInclusion_comp_prSub]

/-- A slice turns a class pulled back from the sphere factor into its pullback along
the constant map. -/
theorem pull_knSlice_knPrS_const (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (p : Sphere n) (t : Hmod2 (TopCat.of (Sphere n)) n) :
    pull (knSlice Y n p) n (pull (knPrS Y n) n t)
      = pull (cmap (ContinuousMap.const Y p)) n t := by
  rw [← pull_comp, knSlice_comp_prS]

/-- A slice kills any class pulled back from the sphere factor, in positive degree. -/
theorem pull_knSlice_knPrS (Y : Type) [TopologicalSpace Y] (n : ℕ) (hn : 1 ≤ n)
    (p : Sphere n) (t : Hmod2 (TopCat.of (Sphere n)) n) :
    pull (knSlice Y n p) n (pull (knPrS Y n) n t) = 0 := by
  rw [← pull_comp, knSlice_comp_prS]
  exact pull_const_eq_zero Y p n hn t

/-! ## 1. The suspension of a sphere class -/

/-- **The suspension of a sphere class**: the Mayer–Vietoris connecting map of the
hemispherical cover, applied to the transport of `t` to the equatorial band. -/
def sphereNext (n : ℕ) (t : Hmod2 (TopCat.of (Sphere n)) n) :
    Hmod2 (TopCat.of (Sphere (n + 1))) (n + 1) :=
  (mvDelta (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) n).hom
    (pull (cmap (bandToSphere n)) n t)

/-! ## 2. The inductive predicate -/

/-- The inductive predicate of the Künneth induction. -/
def KnGen (n : ℕ) (t : Hmod2 (TopCat.of (Sphere n)) n) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ) (v : Hmod2 (TopCat.of Y) m)
    (c : Hmod2 (TopCat.of Y) (n + m)),
    cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m v)
        = pull (knPrY Y n) (n + m) c → v = 0

/-- **In positive degree the inductive predicate is the plain injectivity
statement**: a slice kills the sphere class and retracts the projection, so the
pullback on the right of `KnGen` is forced to vanish. -/
theorem knGen_of_injective (n : ℕ) (hn : 1 ≤ n) (t : Hmod2 (TopCat.of (Sphere n)) n)
    (h : ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ) (v : Hmod2 (TopCat.of Y) m),
      cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m v) = 0 → v = 0) :
    KnGen n t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro Y _ m v c hc
  have hslice := congrArg (pull (knSlice Y (k + 1) (northPole k)) (k + 1 + m)) hc
  rw [pull_cup, pull_knSlice_knPrY, pull_knSlice_knPrY,
    pull_knSlice_knPrS Y (k + 1) hn, zero_cup] at hslice
  refine h Y m v ?_
  rw [hc, ← hslice, pull_zero]

/-! ## 3. The step -/

set_option maxHeartbeats 1000000 in
/-- **The Künneth induction step.**  If `t₀` detects classes on the base up to a
pullback, then its suspension detects them outright. -/
theorem injective_sphereNext (n : ℕ) (t₀ : Hmod2 (TopCat.of (Sphere n)) n)
    (h : KnGen n t₀) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (v : Hmod2 (TopCat.of Y) m)
    (hv : cup (pull (knPrS Y (n + 1)) (n + 1) (sphereNext n t₀))
      (pull (knPrY Y (n + 1)) m v) = 0) : v = 0 := by
  set τ : Hmod2 (TopCat.of ↥(bandSet Y n)) n :=
    pull (bandRestrict Y n) n (pull (cmap (bandToSphere n)) n t₀) with hτ
  -- naturality of `δ` identifies the suspended class
  have hdelta : (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) n).hom τ
      = pull (knPrS Y (n + 1)) (n + 1) (sphereNext n t₀) :=
    MVDelta.mvDelta_naturality (knPrS Y (n + 1)) (upperOpens n) (lowerOpens n)
      (upperOpens_sup_lowerOpens n) n (pull (cmap (bandToSphere n)) n t₀)
  -- δ-linearity
  have hzero : (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (n + m)).hom
      (cup τ (pull (prSub Y n (bandSet Y n)) m v)) = 0 := by
    have hb := MVDelta.mvDelta_cup (hemiU Y n) (hemiV Y n) (hemi_sup Y n) τ
      (pull (knPrY Y (n + 1)) m v)
    rw [pull_sInclusion_knPrY, hdelta, hv, cohCast_zero] at hb
    exact hb
  -- exactness at the intersection
  obtain ⟨a, b, hab⟩ := (mvExactW (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (n + m)
    (cup τ (pull (prSub Y n (bandSet Y n)) m v))).1 hzero
  obtain ⟨c, hc⟩ := exists_pull_prSub_of_res Y n (n + m) _ a b hab
  -- transport to `Y × S^n`
  have key : cup (pull (knPrS Y n) n t₀) (pull (knPrY Y n) m v)
      = pull (knPrY Y n) (n + m) c := by
    refine pull_bandHE_injective Y n (n + m) ?_
    rw [pull_cup, pull_bandHE_knPrS, pull_bandHE_knPrY, pull_bandHE_knPrY, ← hτ, hc]
  exact h Y m v c key

end KnHemi

end

end GroupApproximation.CharClass
