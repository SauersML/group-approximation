import GroupApproximation.CharClass.CohomologyKunnethHemiOf
import GroupApproximation.CharClass.CohomologyKunnethSplitOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth induction predicate over a field, and the suspension of a sphere class

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of the δ-free half of `CohomologyKunnethStep` with coefficients in a field `K`.
The inductive predicate that propagates along the sphere suspension is

```text
KnGenOf K n t : ∀ Y m (v : H^m(Y; K)) (c : H^{n+m}(Y; K)),
    pr_S^* t ⌣ pr_Y^* v = pr_Y^* c → v = 0,
```

and in positive degree it is the plain injectivity statement, because a slice kills `pr_S^* t` and
retracts `pr_Y^*` (`knGen_of_injectiveOf`).

**What is new over `K`.**  Over `F₂` a nonzero class of `H^n(S^n)` *is* the fundamental class.
Over `K` it is a unit multiple of it, so the predicate has to survive rescaling by a nonzero
scalar; `knGenOf_smul` says it does, and that is the only place a field is used beyond the
vanishing of a point's positive cohomology.

The induction step itself, `injective_sphereNextOf`, needs the naturality and the δ-linearity of
the Mayer–Vietoris connecting map over `K` (lane `lix-lh`) and lives in a separate module.

## Main declarations

* `KnHemi.sphereNextOf` — the suspension of a sphere class over `K`.
* `KnHemi.KnGenOf`, `KnHemi.knGen_of_injectiveOf`, `KnHemi.knGenOf_smul`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-! ## 0. Three small facts over `K` -/

theorem pull_sInclusion_knPrYOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (S : Set ↥(prodTop Y n)) (k : ℕ) (v : Hmod K (TopCat.of Y) k) :
    pull (sInclusion S) k (pull (knPrY Y (n + 1)) k v) = pull (prSub Y n S) k v := by
  rw [← pull_comp, sInclusion_comp_prSub]

/-- A slice turns a class pulled back from the sphere factor into its pullback along the
constant map. -/
theorem pull_knSlice_knPrS_constOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (p : Sphere n) (t : Hmod K (TopCat.of (Sphere n)) n) :
    pull (knSlice Y n p) n (pull (knPrS Y n) n t)
      = pull (cmap (ContinuousMap.const Y p)) n t := by
  rw [← pull_comp, knSlice_comp_prS]

/-- A slice kills any class pulled back from the sphere factor, in positive degree. -/
theorem pull_knSlice_knPrSOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (p : Sphere n) (t : Hmod K (TopCat.of (Sphere n)) n) :
    pull (knSlice Y n p) n (pull (knPrS Y n) n t) = 0 := by
  rw [← pull_comp, knSlice_comp_prS]
  exact pull_const_eq_zeroOf K Y p n hn t

/-! ## 1. The suspension of a sphere class -/

/-- **The suspension of a sphere class over `K`**: the Mayer–Vietoris connecting map of the
hemispherical cover, applied to the transport of `t` to the equatorial band. -/
def sphereNextOf (K : Type) [Field K] (n : ℕ) (t : Hmod K (TopCat.of (Sphere n)) n) :
    Hmod K (TopCat.of (Sphere (n + 1))) (n + 1) :=
  (mvDeltaOf K (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) n).hom
    (pull (cmap (bandToSphere n)) n t)

/-! ## 2. The inductive predicate -/

/-- The inductive predicate of the Künneth induction over `K`. -/
def KnGenOf (K : Type) [CommRing K] (n : ℕ) (t : Hmod K (TopCat.of (Sphere n)) n) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ) (v : Hmod K (TopCat.of Y) m)
    (c : Hmod K (TopCat.of Y) (n + m)),
    cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m v) = pull (knPrY Y n) (n + m) c → v = 0

/-- **In positive degree the inductive predicate is the plain injectivity statement**, over `K`. -/
theorem knGen_of_injectiveOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n)
    (t : Hmod K (TopCat.of (Sphere n)) n)
    (h : ∀ (Y : Type) [TopologicalSpace Y] (m : ℕ) (v : Hmod K (TopCat.of Y) m),
      cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m v) = 0 → v = 0) :
    KnGenOf K n t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro Y _ m v c hc
  have hslice := congrArg
    (pull (knSlice Y (k + 1) (SphereOddDegree.northPole k)) (k + 1 + m)) hc
  rw [pull_cup, pull_knSlice_knPrYOf, pull_knSlice_knPrYOf,
    pull_knSlice_knPrSOf K Y (k + 1) hn, zero_cup] at hslice
  refine h Y m v ?_
  rw [hc, ← hslice, pull_zero]

/-- **The predicate survives rescaling by a nonzero scalar.**  Over `F₂` there is nothing to
rescale; over `K` this is what lets the chain of suspended classes reach the fundamental class,
which it only hits up to a unit. -/
theorem knGenOf_smul (K : Type) [Field K] (n : ℕ) (t : Hmod K (TopCat.of (Sphere n)) n)
    (h : KnGenOf K n t) (s : K) (hs : s ≠ 0) : KnGenOf K n (s • t) := by
  intro Y _ m v c hc
  refine h Y m v (s⁻¹ • c) ?_
  rw [pull_smul, cup_smul_left] at hc
  rw [pull_smul, ← hc, smul_smul, inv_mul_cancel₀ hs, one_smul]

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.knGen_of_injectiveOf
#audit_axioms KnHemi.knGenOf_smul

end GroupApproximation.CharClass
