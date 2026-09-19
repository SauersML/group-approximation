import GroupApproximation.CharClass.CohomologyKunnethZero
import GroupApproximation.CharClass.CohomologyKunnethMap
import GroupApproximation.CharClass.CohomologyDegreeZero

/-!
# The Künneth map with a sphere factor is injective

The chain of sphere classes is `zeroGen` on `S⁰` and its iterated suspensions.
`KnGen` propagates along it, and it also forces the class to be nonzero: if the
class were zero, `KnGen` applied to a point with the unit class would say that
`1 = 0` in `H⁰(pt; F₂)`.  Since `H^n(S^n; F₂)` is one dimensional over `F₂` for
`n ≥ 1`, a nonzero class **is** the mod-2 fundamental class, so the chain reaches
`sphereTopClass` and `KunnethSecondInjective` follows.

Together with `kunnethInjective_of_second` this makes the Künneth map with one
sphere factor injective in every degree.

## Main results

* `KnHemi.sphereGen`, `KnHemi.knGen_sphereGen` — the chain and its property.
* `KnHemi.ne_zero_of_knGen` — the predicate forces the class to be nonzero.
* `KnHemi.sphereGen_eq_top` — the chain is the mod-2 fundamental class.
* `KnHemi.kunnethSecondInjective` — the goal.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- The chain of sphere classes: the generator of `H⁰(S⁰; F₂)` and its iterated
suspensions. -/
def sphereGen : (n : ℕ) → Hmod2 (TopCat.of (Sphere n)) n
  | 0 => zeroGen
  | n + 1 => sphereNext n (sphereGen n)

theorem knGen_sphereGen (n : ℕ) : KnGen n (sphereGen n) := by
  induction n with
  | zero => exact knGen_zeroGen
  | succ k ih =>
    refine knGen_of_injective (k + 1) (by omega) (sphereGen (k + 1)) ?_
    intro Y _ m v hv
    exact injective_sphereNext k (sphereGen k) ih Y m v hv

/-- **The inductive predicate forces the class to be nonzero.**  Otherwise it would
say that the unit class of a point vanishes. -/
theorem ne_zero_of_knGen (n : ℕ) (t : Hmod2 (TopCat.of (Sphere n)) n) (h : KnGen n t) :
    t ≠ 0 := by
  intro ht
  haveI : Nonempty ↥(TopCat.of Unit) := ⟨()⟩
  have hzero : cup (pull (knPrS Unit n) n t)
      (pull (knPrY Unit n) 0 (one (TopCat.of Unit)))
      = pull (knPrY Unit n) (n + 0) 0 := by
    rw [ht, pull_zero, zero_cup, pull_zero]
  exact one_ne_zero_cohZero (TopCat.of Unit)
    (h Unit 0 (one (TopCat.of Unit)) 0 hzero)

/-- In `H^n(S^n; F₂)`, `n ≥ 1`, there is exactly one nonzero class. -/
theorem sphere_coh_top_eq_of_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (a : Hmod2 (TopCat.of (Sphere n)) n) (ha : a ≠ 0) : a = sphereTopClass n hn := by
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hne : (sphereTopEquiv n hn) a ≠ 0 := by
    intro h0
    refine ha ?_
    have hb := (sphereTopEquiv n hn).symm_apply_apply a
    rw [h0, map_zero] at hb
    exact hb.symm
  rw [sphere_coh_top_eq_smul n hn a, hz _ hne, one_smul]

/-- The chain reaches the mod-2 fundamental class. -/
theorem sphereGen_eq_top (n : ℕ) (hn : 1 ≤ n) : sphereGen n = sphereTopClass n hn :=
  sphere_coh_top_eq_of_ne_zero n hn (sphereGen n)
    (ne_zero_of_knGen n (sphereGen n) (knGen_sphereGen n))

/-- **The second component of the Künneth map with a sphere factor is injective.** -/
theorem kunnethSecondInjective (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    KunnethSecondInjective Y n := by
  intro hn m v hv
  refine knGen_sphereGen n Y m v 0 ?_
  rw [sphereGen_eq_top n hn, pull_zero]
  exact hv

/-- **The Künneth map with a sphere factor is injective.** -/
theorem kunnethInjective (Y : Type) [TopologicalSpace Y] (n : ℕ) (p : Sphere n)
    (hn : 1 ≤ n) (m : ℕ) (u : Hmod2 (TopCat.of Y) (n + m)) (v : Hmod2 (TopCat.of Y) m)
    (h : kunnethMap Y n hn m u v = 0) : u = 0 ∧ v = 0 :=
  kunnethInjective_of_second Y n p (kunnethSecondInjective Y n) hn m u v h

end KnHemi

end

end GroupApproximation.CharClass
