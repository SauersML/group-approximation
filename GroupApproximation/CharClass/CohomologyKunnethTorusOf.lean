import GroupApproximation.CharClass.CohomologyKunnethDecompOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Künneth uniqueness for the two sphere factors of the mapping-torus base, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.4, the field `z_inj` of
`Gen.RealTorusModP`).

The even side of Step D mod `p` asks that the `z = t x`-coordinate of a class of
`H^*(S¹ × S^{2n+1} × Y; K)` be well defined: `ι u + t x ι v = 0 → v = 0`.  Degreewise that is
Künneth injectivity for **two** sphere factors, and it comes from the one-factor statement
`KnHemi.kunnethSecondInjectiveOf` applied twice, peeling one sphere at a time, as in the `F₂`
file `CohomologyParityKunneth` at rank two.

The base is left-nested, `(Y × S^{2n+1}) × S¹`, because the one-factor lemma puts the new sphere
on the right.  A slice of the circle factor kills `t`, which forces the `ι u` summand to vanish;
what is left is one application of the one-factor lemma over `Y × S^{2n+1}`, then one over `Y`.

**Any nonzero sphere classes.**  Over `F₂` the only nonzero top class of a sphere is the
fundamental class.  Over `K` a consumer may hold any nonzero class; it is a unit multiple of the
fundamental class, so the one-factor lemma holds for it too (`kunnethSecondInjective_of_ne_zeroOf`).

The degreewise statement is stated in the shape of the hypothesis of `Gen.tx_inj_of_degreewise`
(right-associated cup, degree `1 + ((2n + 1) + c)`), so the ring-level field is a componentwise
reading of it.

## Main declarations

* `KnHemi.kunnethSecondInjective_of_ne_zeroOf` — one sphere factor, any nonzero top class.
* `KnTwo.midBaseOf`, `KnTwo.torusBaseOf`, `KnTwo.prYOf`, `KnTwo.prS1Of`, `KnTwo.prSoddOf` — the
  model and its three projections; `KnTwo.sig1Of`, `KnTwo.sigOddOf` — the two sphere classes.
* `KnTwo.tx_inj_degree_of_ne_zeroOf` — the degreewise statement for any nonzero sphere classes.
* `KnTwo.tx_inj_degreeOf` — **the degreewise Künneth uniqueness for `z = t x`**, at the
  fundamental classes.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- **One sphere factor, any nonzero top class.**  If `t ≠ 0` in `H^n(S^n; K)` and
`pr_S^* t ⌣ pr_Y^* v = 0`, then `v = 0`: `t` is a unit multiple of the fundamental class. -/
theorem kunnethSecondInjective_of_ne_zeroOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (hn : 1 ≤ n) (t : Hmod K (TopCat.of (Sphere n)) n) (ht : t ≠ 0) (m : ℕ)
    (v : Hmod K (TopCat.of Y) m)
    (hv : cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m v) = 0) : v = 0 := by
  have hsm := sphere_coh_top_eq_smulOf K n hn t
  obtain ⟨c, hc⟩ : ∃ c : K, sphereTopEquivOf K n hn t = c := ⟨_, rfl⟩
  rw [hc] at hsm
  have hc0 : c ≠ 0 := fun h0 => ht (by rw [hsm, h0, zero_smul])
  rw [hsm, pull_smul, cup_smul_left] at hv
  have hv' : cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m v) = 0 := by
    have hh : c⁻¹ • (c • cup (pull (knPrS Y n) n (sphereTopClassOf K n hn))
          (pull (knPrY Y n) m v))
        = c⁻¹ • (0 : Hmod K (TopCat.of (Y × Sphere n)) (n + m)) := by
      rw [hv]
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul, smul_zero] at hh
  exact kunnethSecondInjectiveOf K Y n hn m v hv'

end KnHemi

namespace KnTwo

/-! ## 1. The model, its projections and its two sphere classes -/

/-- The intermediate base `Y × S^{2n+1}`. -/
abbrev midBaseOf (Y : Type) [TopologicalSpace Y] (n : ℕ) : Type := Y × Sphere (2 * n + 1)

/-- The mapping-torus base, left-nested as `(Y × S^{2n+1}) × S¹`. -/
abbrev torusBaseOf (Y : Type) [TopologicalSpace Y] (n : ℕ) : Type := midBaseOf Y n × Sphere 1

/-- The projection to `Y`. -/
def prYOf (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    TopCat.of (torusBaseOf Y n) ⟶ TopCat.of Y :=
  knPrY (midBaseOf Y n) 1 ≫ knPrY Y (2 * n + 1)

/-- The projection to the circle factor. -/
def prS1Of (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    TopCat.of (torusBaseOf Y n) ⟶ TopCat.of (Sphere 1) :=
  knPrS (midBaseOf Y n) 1

/-- The projection to the odd sphere factor. -/
def prSoddOf (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    TopCat.of (torusBaseOf Y n) ⟶ TopCat.of (Sphere (2 * n + 1)) :=
  knPrY (midBaseOf Y n) 1 ≫ knPrS Y (2 * n + 1)

/-- The degree-one class `t` on the base, over `K`. -/
def sig1Of (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Hmod K (TopCat.of (torusBaseOf Y n)) 1 :=
  pull (prS1Of Y n) 1 (sphereTopClassOf K 1 (by omega))

/-- The degree-`(2n+1)` class `x` on the base, over `K`. -/
def sigOddOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Hmod K (TopCat.of (torusBaseOf Y n)) (2 * n + 1) :=
  pull (prSoddOf Y n) (2 * n + 1) (sphereTopClassOf K (2 * n + 1) (by omega))

/-! ## 2. The degreewise statement -/

set_option maxHeartbeats 1000000 in
/-- **Künneth uniqueness for `z = t x` over a field, in a single degree, for any nonzero sphere
classes.**  For nonzero top classes `σ₁` of `S¹` and `σodd` of `S^{2n+1}`, if
`pr_Y^* α + pr_{S¹}^* σ₁ ⌣ (pr_{S^{2n+1}}^* σodd ⌣ pr_Y^* β) = 0` then `β = 0`. -/
theorem tx_inj_degree_of_ne_zeroOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (σ₁ : Hmod K (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : Hmod K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) (hσodd : σodd ≠ 0)
    (c : ℕ) (α : Hmod K (TopCat.of Y) (1 + ((2 * n + 1) + c))) (β : Hmod K (TopCat.of Y) c)
    (h : pull (prYOf Y n) (1 + ((2 * n + 1) + c)) α
      + cup (pull (prS1Of Y n) 1 σ₁)
          (cup (pull (prSoddOf Y n) (2 * n + 1) σodd) (pull (prYOf Y n) c β)) = 0) :
    β = 0 := by
  have hslice : ∀ (k : ℕ) (a : Hmod K (TopCat.of Y) k),
      pull (knSlice (midBaseOf Y n) 1
          (GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.northPole 0)) k
          (pull (prYOf Y n) k a)
        = pull (knPrY Y (2 * n + 1)) k a := by
    intro k a
    rw [prYOf, pull_comp, pull_knSlice_knPrYOf]
  have hs1 : pull (knSlice (midBaseOf Y n) 1
        (GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.northPole 0)) 1
        (pull (prS1Of Y n) 1 σ₁) = 0 :=
    KnHemi.pull_knSlice_knPrSOf K (midBaseOf Y n) 1 (by omega)
      (GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.northPole 0) σ₁
  -- the circle slice kills the `t x` term, so the first summand vanishes
  have hU : pull (knPrY Y (2 * n + 1)) (1 + ((2 * n + 1) + c)) α = 0 := by
    have hh := congrArg (pull (knSlice (midBaseOf Y n) 1
      (GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.northPole 0))
        (1 + ((2 * n + 1) + c))) h
    rw [pull_add, pull_zero, hslice, pull_cup, hs1, zero_cup, add_zero] at hh
    exact hh
  have h2 : cup (pull (prS1Of Y n) 1 σ₁)
      (cup (pull (prSoddOf Y n) (2 * n + 1) σodd) (pull (prYOf Y n) c β)) = 0 := by
    have hz : pull (prYOf Y n) (1 + ((2 * n + 1) + c)) α = 0 := by
      rw [prYOf, pull_comp, hU, pull_zero]
    rwa [hz, zero_add] at h
  have h4 : cup (pull (prSoddOf Y n) (2 * n + 1) σodd) (pull (prYOf Y n) c β)
      = pull (knPrY (midBaseOf Y n) 1) ((2 * n + 1) + c)
          (cup (pull (knPrS Y (2 * n + 1)) (2 * n + 1) σodd)
            (pull (knPrY Y (2 * n + 1)) c β)) := by
    rw [pull_cup, prSoddOf, prYOf, pull_comp, pull_comp]
  -- peel the circle factor, then the odd sphere
  have h5 : cup (pull (knPrS Y (2 * n + 1)) (2 * n + 1) σodd)
      (pull (knPrY Y (2 * n + 1)) c β) = 0 := by
    refine KnHemi.kunnethSecondInjective_of_ne_zeroOf K (midBaseOf Y n) 1 (by omega) σ₁ hσ₁
      ((2 * n + 1) + c) _ ?_
    rw [← h4]
    exact h2
  exact KnHemi.kunnethSecondInjective_of_ne_zeroOf K Y (2 * n + 1) (by omega) σodd hσodd c β h5

/-- **Künneth uniqueness for `z = t x` over a field, in a single degree.**  If
`pr_Y^* uu + t ⌣ (x ⌣ pr_Y^* vv) = 0` on `(Y × S^{2n+1}) × S¹` then `vv = 0`. -/
theorem tx_inj_degreeOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n c : ℕ)
    (uu : Hmod K (TopCat.of Y) (1 + ((2 * n + 1) + c))) (vv : Hmod K (TopCat.of Y) c)
    (h : pull (prYOf Y n) (1 + ((2 * n + 1) + c)) uu
        + cup (sig1Of K Y n) (cup (sigOddOf K Y n) (pull (prYOf Y n) c vv)) = 0) :
    vv = 0 :=
  tx_inj_degree_of_ne_zeroOf K Y n (sphereTopClassOf K 1 (by omega))
    (sphereTopClassOf_ne_zero K 1 (by omega)) (sphereTopClassOf K (2 * n + 1) (by omega))
    (sphereTopClassOf_ne_zero K (2 * n + 1) (by omega)) c uu vv h

end KnTwo

end

/-! Audited on every build. -/

#audit_axioms KnHemi.kunnethSecondInjective_of_ne_zeroOf
#audit_axioms KnTwo.tx_inj_degree_of_ne_zeroOf
#audit_axioms KnTwo.tx_inj_degreeOf

end GroupApproximation.CharClass
