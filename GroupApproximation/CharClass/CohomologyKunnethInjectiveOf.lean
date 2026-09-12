import GroupApproximation.CharClass.CohomologyKunnethStepDeltaOf
import GroupApproximation.CharClass.CohomologyKunnethZeroOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth map with a sphere factor is injective, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethInjective` with coefficients in a field `K`.  The chain of
sphere classes `sphereGenOf K` is `zeroGenOf K` on `S⁰` and its iterated suspensions; `KnGenOf`
propagates along it (`knGen_zeroGenOf`, `injective_sphereNextOf`) and forces every link to be
nonzero.

**What changes over `K`.**  Over `F₂` a nonzero class of `H^n(S^n)` is the fundamental class, so the
chain *reaches* `sphereTopClass`.  Over `K` a nonzero class is a unit multiple of
`sphereTopClassOf K n hn` (`KroneckerSphere.sphere_coh_top_eq_smulOf`), and the predicate survives
rescaling (`knGenOf_smul`), so it holds of the fundamental class itself.  The nonvanishing of the
unit class of a point over `K` is proved here from `H⁰(pt; K) ≅ K`.

## Main results

* `KnHemi.sphereGenOf`, `KnHemi.knGen_sphereGenOf`, `KnHemi.ne_zero_of_knGenOf`.
* `KnHemi.knGen_sphereTopClassOf` — the predicate holds of the fundamental class over `K`.
* `KnHemi.kunnethSecondInjectiveOf`, `KnHemi.kunnethInjectiveOf` — **the goal**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- The unit class of a point is nonzero over any field: `H⁰(pt; K) ≅ K`. -/
theorem one_ne_zero_unitOf (K : Type) [Field K] :
    one (TopCat.of Unit) ≠ (0 : Hmod K (TopCat.of Unit) 0) := by
  intro h
  have hall : ∀ a : Hmod K (TopCat.of Unit) 0, a = 0 := by
    intro a
    have ha := one_cup a
    rw [h, zero_cup, CharClass.cohCast_zero] at ha
    exact ha.symm
  have h1 : (cohZeroEquivOfContractibleOf K Unit).symm 1
      = (cohZeroEquivOfContractibleOf K Unit).symm 0 :=
    (hall _).trans (hall _).symm
  exact one_ne_zero ((cohZeroEquivOfContractibleOf K Unit).symm.injective h1)

/-- The chain of sphere classes over `K`. -/
def sphereGenOf (K : Type) [Field K] : (n : ℕ) → Hmod K (TopCat.of (Sphere n)) n
  | 0 => zeroGenOf K
  | n + 1 => sphereNextOf K n (sphereGenOf K n)

theorem knGen_sphereGenOf (K : Type) [Field K] (n : ℕ) : KnGenOf K n (sphereGenOf K n) := by
  induction n with
  | zero => exact knGen_zeroGenOf K
  | succ k ih =>
    refine knGen_of_injectiveOf K (k + 1) (by omega) (sphereGenOf K (k + 1)) ?_
    intro Y _ m v hv
    exact injective_sphereNextOf K k (sphereGenOf K k) ih Y m v hv

/-- **The inductive predicate forces the class to be nonzero**, over `K`. -/
theorem ne_zero_of_knGenOf (K : Type) [Field K] (n : ℕ) (t : Hmod K (TopCat.of (Sphere n)) n)
    (h : KnGenOf K n t) : t ≠ 0 := by
  intro ht
  have hzero : cup (pull (knPrS Unit n) n t) (pull (knPrY Unit n) 0 (one (TopCat.of Unit)))
      = pull (knPrY Unit n) (n + 0) (0 : Hmod K (TopCat.of Unit) (n + 0)) := by
    rw [ht, pull_zero, zero_cup, pull_zero]
  exact one_ne_zero_unitOf K (h Unit 0 (one (TopCat.of Unit)) 0 hzero)

/-- **The predicate holds of the fundamental class over `K`.**  The chain reaches a nonzero
multiple of it, and the predicate survives rescaling by the inverse. -/
theorem knGen_sphereTopClassOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    KnGenOf K n (sphereTopClassOf K n hn) := by
  have hne := ne_zero_of_knGenOf K n (sphereGenOf K n) (knGen_sphereGenOf K n)
  have hsm := sphere_coh_top_eq_smulOf K n hn (sphereGenOf K n)
  obtain ⟨c, hc⟩ : ∃ c : K, sphereTopEquivOf K n hn (sphereGenOf K n) = c := ⟨_, rfl⟩
  rw [hc] at hsm
  have hc0 : c ≠ 0 := fun h0 => hne (by rw [hsm, h0, zero_smul])
  have heq : sphereTopClassOf K n hn = c⁻¹ • sphereGenOf K n := by
    rw [hsm, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [heq]
  exact knGenOf_smul K n (sphereGenOf K n) (knGen_sphereGenOf K n) c⁻¹ (inv_ne_zero hc0)

/-- **The second component of the Künneth map with a sphere factor is injective, over `K`.** -/
theorem kunnethSecondInjectiveOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    KunnethSecondInjectiveOf K Y n := by
  intro hn m v hv
  refine knGen_sphereTopClassOf K n hn Y m v 0 ?_
  rw [pull_zero]
  exact hv

/-- **The Künneth map with a sphere factor is injective, over `K`.** -/
theorem kunnethInjectiveOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (p : Sphere n) (hn : 1 ≤ n) (m : ℕ) (u : Hmod K (TopCat.of Y) (n + m))
    (v : Hmod K (TopCat.of Y) m) (h : kunnethMapOf K Y n hn m u v = 0) : u = 0 ∧ v = 0 :=
  kunnethInjective_of_secondOf K Y n p (kunnethSecondInjectiveOf K Y n) hn m u v h

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.kunnethSecondInjectiveOf
#audit_axioms KnHemi.kunnethInjectiveOf

end GroupApproximation.CharClass
