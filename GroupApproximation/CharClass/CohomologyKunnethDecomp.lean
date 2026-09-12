import GroupApproximation.CharClass.CohomologyKunnethSurjZero
import GroupApproximation.CharClass.CohomologyKunnethInjective

/-!
# The Künneth decomposition with one sphere factor

The induction closes: `KnLow` is vacuous at the zero sphere and propagates, and
`KnTop` holds at the zero sphere for `zeroGen` and propagates along the chain of
suspensions, which is the mod-2 fundamental class from dimension one on.

So every class on `Y × S^n` in degree below `n` is pulled back from `Y`, and every
class in degree `n + m` is a pullback plus the fundamental class cupped with a
pullback.  With `KnHemi.kunnethSecondInjective` the two coefficients are unique.

## Main results

* `KnHemi.kunneth_low` — below the sphere dimension, everything is pulled back.
* `KnHemi.kunneth_decomposition` — the splitting in degree `n + m`.
* `KnHemi.kunneth_decomposition_unique` — the second coefficient is unique.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

theorem knLow_all (n : ℕ) : KnLow n := by
  induction n with
  | zero => intro Y _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ k ih => exact knLow_succ k ih

theorem knTop_sphereGen (n : ℕ) : KnTop n (sphereGen n) := by
  induction n with
  | zero => exact KnZero.knTop_zero
  | succ k ih => exact knTop_succ k (sphereGen k) ih

theorem knTop_sphereTopClass (n : ℕ) (hn : 1 ≤ n) : KnTop n (sphereTopClass n hn) := by
  rw [← sphereGen_eq_top n hn]
  exact knTop_sphereGen n

/-! ## The consumer-facing statements -/

/-- **Below the sphere dimension every class is pulled back from the base.** -/
theorem kunneth_low (Y : Type) [TopologicalSpace Y] (n k : ℕ) (hk : k < n)
    (z : Hmod2 (TopCat.of (Y × Sphere n)) k) :
    ∃ a : Hmod2 (TopCat.of Y) k, z = pull (knPrY Y n) k a :=
  knLow_all n Y k hk z

/-- **The Künneth decomposition with one sphere factor.**  In degree `n + m` every
class is a pullback from the base plus the mod-2 fundamental class of the sphere
cupped with a pullback. -/
theorem kunneth_decomposition (Y : Type) [TopologicalSpace Y] (n : ℕ) (hn : 1 ≤ n)
    (k m : ℕ) (hk : n + m = k) (z : Hmod2 (TopCat.of (Y × Sphere n)) k) :
    ∃ (a : Hmod2 (TopCat.of Y) k) (b : Hmod2 (TopCat.of Y) m),
      z = pull (knPrY Y n) k a
        + cohCast hk (cup (knSigma Y n hn) (pull (knPrY Y n) m b)) :=
  knTop_sphereTopClass n hn Y k m hk z

/-- **The second coefficient of the decomposition is unique.** -/
theorem kunneth_decomposition_unique (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (k m : ℕ) (hk : n + m = k)
    (a a' : Hmod2 (TopCat.of Y) k) (b b' : Hmod2 (TopCat.of Y) m)
    (h : pull (knPrY Y n) k a
          + cohCast hk (cup (knSigma Y n hn) (pull (knPrY Y n) m b))
        = pull (knPrY Y n) k a'
          + cohCast hk (cup (knSigma Y n hn) (pull (knPrY Y n) m b'))) :
    b = b' := by
  subst hk
  rw [cohCast_self, cohCast_self] at h
  have h2 : (pull (knPrY Y n) (n + m) a
        + cup (knSigma Y n hn) (pull (knPrY Y n) m b))
      + (pull (knPrY Y n) (n + m) a'
        + cup (knSigma Y n hn) (pull (knPrY Y n) m b')) = 0 := by
    rw [h, add_self_eq_zero_two]
  have hz : kunnethMap Y n hn m (a + a') (b + b') = 0 := by
    rw [kunnethMap_eq, pull_add, pull_add, cup_add_right, ← h2]
    abel
  have hbb : b + b' = 0 :=
    (kunnethInjective_of_second Y n (spherePoint n) (kunnethSecondInjective Y n)
      hn m (a + a') (b + b') hz).2
  have hfin := congrArg (fun y => y + b') hbb
  simpa only [add_assoc, add_self_eq_zero_two, add_zero, zero_add] using hfin

end KnHemi

end

end GroupApproximation.CharClass
