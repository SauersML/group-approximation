import GroupApproximation.CharClass.CohomologyKunnethSurjZeroOf
import GroupApproximation.CharClass.CohomologyKunnethInjectiveOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth decomposition with one sphere factor, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethDecomp` with coefficients in a field `K`.  The induction closes:
`KnLowOf` is vacuous at the zero sphere and propagates (`knLow_succOf`), and `KnTopOf` holds at the
zero sphere for `zeroGenOf K` (`KnZero.knTop_zeroOf`) and propagates along the chain of
suspensions (`knTop_succOf`).

**What changes over `K`.**  Over `F₂` the chain of suspensions *is* the fundamental class from
dimension one on.  Over `K` it is a nonzero multiple of it (`sphereTopClassOf_eq_smul_sphereGenOf`),
and `KnTopOf` survives rescaling by a nonzero scalar (`knTopOf_smul`: rescale the second
coefficient by the inverse), so the decomposition holds with the fundamental class itself.
Uniqueness subtracts where the `F₂` file adds.

## Main results

* `KnHemi.knLow_allOf`, `KnHemi.knTop_sphereGenOf`, `KnHemi.knTopOf_smul`,
  `KnHemi.sphereTopClassOf_eq_smul_sphereGenOf`, `KnHemi.knTop_sphereTopClassOf`.
* `KnHemi.kunneth_lowOf` — below the sphere dimension, everything is pulled back.
* `KnHemi.kunneth_decompositionOf` — the splitting in degree `n + m`.
* `KnHemi.kunneth_decomposition_uniqueOf` — the second coefficient is unique.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

theorem knLow_allOf (K : Type) [Field K] (n : ℕ) : KnLowOf K n := by
  induction n with
  | zero => intro Y _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ k ih => exact knLow_succOf K k ih

theorem knTop_sphereGenOf (K : Type) [Field K] (n : ℕ) : KnTopOf K n (sphereGenOf K n) := by
  induction n with
  | zero => exact KnZero.knTop_zeroOf K
  | succ k ih => exact knTop_succOf K k (sphereGenOf K k) ih

/-- **The top half survives rescaling by a nonzero scalar**: rescale the second coefficient by the
inverse. -/
theorem knTopOf_smul (K : Type) [Field K] (n : ℕ) (t : Hmod K (TopCat.of (Sphere n)) n)
    (h : KnTopOf K n t) (s : K) (hs : s ≠ 0) : KnTopOf K n (s • t) := by
  intro Y _ k m hk z
  obtain ⟨a, b, hab⟩ := h Y k m hk z
  refine ⟨a, s⁻¹ • b, ?_⟩
  rw [hab, pull_smul, pull_smul, cup_smul_left, cup_smul_right, smul_smul, mul_inv_cancel₀ hs,
    one_smul]

/-- The fundamental class over `K` is a nonzero multiple of the chain of suspensions. -/
theorem sphereTopClassOf_eq_smul_sphereGenOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : K, c ≠ 0 ∧ sphereTopClassOf K n hn = c • sphereGenOf K n := by
  have hne := ne_zero_of_knGenOf K n (sphereGenOf K n) (knGen_sphereGenOf K n)
  have hsm := sphere_coh_top_eq_smulOf K n hn (sphereGenOf K n)
  obtain ⟨c, hc⟩ : ∃ c : K, sphereTopEquivOf K n hn (sphereGenOf K n) = c := ⟨_, rfl⟩
  rw [hc] at hsm
  have hc0 : c ≠ 0 := fun h0 => hne (by rw [hsm, h0, zero_smul])
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  rw [hsm, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem knTop_sphereTopClassOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    KnTopOf K n (sphereTopClassOf K n hn) := by
  obtain ⟨c, hc, heq⟩ := sphereTopClassOf_eq_smul_sphereGenOf K n hn
  rw [heq]
  exact knTopOf_smul K n _ (knTop_sphereGenOf K n) c hc

/-! ## The consumer-facing statements -/

/-- **Below the sphere dimension every class is pulled back from the base**, over `K`. -/
theorem kunneth_lowOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (hk : k < n) (z : Hmod K (TopCat.of (Y × Sphere n)) k) :
    ∃ a : Hmod K (TopCat.of Y) k, z = pull (knPrY Y n) k a :=
  knLow_allOf K n Y k hk z

/-- **The Künneth decomposition with one sphere factor, over `K`.**  In degree `n + m` every class
is a pullback from the base plus the fundamental class of the sphere cupped with a pullback. -/
theorem kunneth_decompositionOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (k m : ℕ) (hk : n + m = k) (z : Hmod K (TopCat.of (Y × Sphere n)) k) :
    ∃ (a : Hmod K (TopCat.of Y) k) (b : Hmod K (TopCat.of Y) m),
      z = pull (knPrY Y n) k a
        + cohCast hk (cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m b)) :=
  knTop_sphereTopClassOf K n hn Y k m hk z

/-- **The second coefficient of the decomposition is unique**, over `K`. -/
theorem kunneth_decomposition_uniqueOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (hn : 1 ≤ n) (k m : ℕ) (hk : n + m = k)
    (a a' : Hmod K (TopCat.of Y) k) (b b' : Hmod K (TopCat.of Y) m)
    (h : pull (knPrY Y n) k a
          + cohCast hk (cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m b))
        = pull (knPrY Y n) k a'
          + cohCast hk (cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m b'))) :
    b = b' := by
  subst hk
  rw [CharClass.cohCast_self, CharClass.cohCast_self] at h
  have hsubY : ∀ (j : ℕ) (x y : Hmod K (TopCat.of Y) j),
      pull (knPrY Y n) j (x - y) = pull (knPrY Y n) j x - pull (knPrY Y n) j y := by
    intro j x y
    simpa only [pullLinear_apply] using map_sub (pullLinear (knPrY Y n) j) x y
  have hsubC : ∀ (x y : Hmod K (TopCat.of (Y × Sphere n)) m),
      cup (knSigmaOf K Y n hn) (x - y)
        = cup (knSigmaOf K Y n hn) x - cup (knSigmaOf K Y n hn) y := by
    intro x y
    simpa only [cupBilin_apply] using
      map_sub (cupBilin (TopCat.of (Y × Sphere n)) n m (knSigmaOf K Y n hn)) x y
  have hz : kunnethMapOf K Y n hn m (a - a') (b - b') = 0 := by
    have hexp : kunnethMapOf K Y n hn m (a - a') (b - b')
        = (pull (knPrY Y n) (n + m) a + cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m b))
          - (pull (knPrY Y n) (n + m) a' + cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m b')) := by
      rw [kunnethMapOf_eq, hsubY, hsubY, hsubC]
      abel
    rw [hexp, h, sub_self]
  have hbb : b - b' = 0 :=
    (kunnethInjective_of_secondOf K Y n (spherePoint n) (kunnethSecondInjectiveOf K Y n) hn m
      (a - a') (b - b') hz).2
  exact sub_eq_zero.1 hbb

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.kunneth_lowOf
#audit_axioms KnHemi.kunneth_decompositionOf
#audit_axioms KnHemi.kunneth_decomposition_uniqueOf

end GroupApproximation.CharClass
