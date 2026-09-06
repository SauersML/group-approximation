import GroupApproximation.CharClass.RelativeLocal
import GroupApproximation.CharClass.CohomologySphere
import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.CharClass.CohomologyBridge
import GroupApproximation.AlgTop.PuncturedNormedSphere

/-!
# The local model `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂) ≅ F₂`

This is item **(B6)** of `cc-thom`'s request
(`notes/lix-lane-reports/cc-thom.md` §"From `cc-relative`"): the relative
cohomology of the pair `(ℂ^r, ℂ^r ∖ 0)` in degree `2r` is one dimensional over
`F₂`, with a named nonzero generator.  It is what turns "the section is a local
homeomorphism at its zero" into "the local class is *the* generator", with no
degree computation anywhere.

For `r = d + 1` the route is the long exact sequence of the pair plus one
homotopy equivalence, and every input is already green:

* `ℂ^r` is a real topological vector space, hence contractible, so its cohomology
  vanishes in the two consecutive degrees `2d+1` and `2d+2`
  (`cc-cohom-api`'s `cohomology_isZero_of_contractible`);
* therefore the connecting map of the pair is an isomorphism
  `H^{2d+1}(ℂ^r ∖ 0) ≅ H^{2d+2}(ℂ^r, ℂ^r ∖ 0)` (`RelativeLES.relDeltaIso`);
* `ℂ^{d+1} ∖ 0` is homotopy equivalent to `S^{2d+1}`
  (`AlgTop.complexPuncturedHomotopyEquivSphere`, fleet-green — not reproved here);
* and `H^{2d+1}(S^{2d+1}; F₂) ≅ F₂` (`cc-cohom-api`'s `sphereTopEquiv`).

Two definitional identifications carry the retyping and are used without a cast:
`↥({0}ᶜ)` is `{w // w ≠ 0}` because membership in a singleton complement unfolds
to `≠`, and `Sphere (2d+1)` is the unit sphere of `EuclideanSpace ℝ (Fin (2*(d+1)))`
because `Nat.mul` recurses on its second argument, so `2*(d+1)` and `(2*d+1)+1`
are the same numeral.

The case `r = 0` is a genuinely different and easier argument, kept separate: the
punctured space is empty, so the pair collapses by `RelativeLES.relEmptyIso` and
the answer is `H^0` of a one-point space.

## Main definitions

* `localEquiv r : H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂) ≃ₗ[F₂] F₂`.
* `localGenerator r` — the class corresponding to `1`.

## Main results

* `localGenerator_ne_zero`, `localEquiv_localGenerator`.
* `relCohomologySetCongr` — transport of relative cohomology along an equality of
  subspaces, used for the `r = 0` collapse and generally useful.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 0. Transport along an equality of subspaces -/

/-- Relative cohomology transported along an equality of the subspace. -/
def relCohomologySetCongr (R : Type) [CommRing R] (X : TopCat.{0}) {A B : Set X}
    (h : A = B) (n : ℕ) : relCohomology R X A n ≅ relCohomology R X B n :=
  eqToIso (by rw [h])

/-! ## 1. The punctured space and the sphere -/

theorem one_le_two_mul_succ (d : ℕ) : 1 ≤ 2 * d + 1 := by omega

/-- **`ℂ^{d+1} ∖ 0` is homotopy equivalent to `S^{2d+1}`.**  This is the
fleet-green `AlgTop.complexPuncturedHomotopyEquivSphere`, retyped through the two
definitional identifications described in the module docstring. -/
def puncturedEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥({(0 : Fin (d + 1) → ℂ)}ᶜ) (Sphere (2 * d + 1)) :=
  AlgTop.complexPuncturedHomotopyEquivSphere d

/-- The cohomology of the punctured space in the sphere's top degree is `F₂`. -/
def puncturedTopEquiv (d : ℕ) :
    Hmod2 (TopCat.of ↥({(0 : Fin (d + 1) → ℂ)}ᶜ)) (2 * d + 1) ≃ₗ[ZMod 2] ZMod 2 :=
  (pullEquivOfHomotopyEquiv (puncturedEquivSphere d) (2 * d + 1)).symm.trans
    (sphereTopEquiv (2 * d + 1) (one_le_two_mul_succ d))

/-! ## 2. The ambient space is contractible -/

theorem isZero_complexSpace_cohomology (r k : ℕ) (hk : 1 ≤ k) :
    IsZero ((cochainCx (ZMod 2) (TopCat.of (Fin r → ℂ))).homology k) :=
  cohomology_isZero_of_contractible (Fin r → ℂ) k hk

/-! ## 3. The connecting isomorphism of the pair -/

/-- The connecting map of the pair `(ℂ^{d+1}, ℂ^{d+1} ∖ 0)` is an isomorphism in
the relevant degree, both neighbouring absolute groups being zero. -/
def puncturedDeltaIso (d : ℕ) :
    Hmod2 (TopCat.of ↥({(0 : Fin (d + 1) → ℂ)}ᶜ)) (2 * d + 1)
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (d + 1) → ℂ))
          ({(0 : Fin (d + 1) → ℂ)}ᶜ) (2 * (d + 1)) :=
  relDeltaIso (ZMod 2) (TopCat.of (Fin (d + 1) → ℂ)) ({(0 : Fin (d + 1) → ℂ)}ᶜ)
    (2 * d + 1)
    (isZero_complexSpace_cohomology (d + 1) (2 * d + 1) (one_le_two_mul_succ d))
    (isZero_complexSpace_cohomology (d + 1) (2 * d + 1 + 1) (by omega))

/-! ## 4. The degenerate case `r = 0` -/

theorem compl_zero_eq_empty :
    ({(0 : Fin 0 → ℂ)}ᶜ : Set (Fin 0 → ℂ)) = ∅ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact funext fun i => i.elim0

/-! ## 5. The local model -/

/-- **(B6)** `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂) ≅ F₂`. -/
def localEquiv : (r : ℕ) →
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r)
      ≃ₗ[ZMod 2] ZMod 2
  | 0 =>
      (relCohomologySetCongr (ZMod 2) (TopCat.of (Fin 0 → ℂ))
          compl_zero_eq_empty 0).toLinearEquiv.trans
        ((relEmptyIso (ZMod 2) (TopCat.of (Fin 0 → ℂ)) 0).toLinearEquiv.trans
          (cohZeroEquivOfContractible (Fin 0 → ℂ)))
  | (d + 1) =>
      (puncturedDeltaIso d).symm.toLinearEquiv.trans (puncturedTopEquiv d)

/-- **(B6)** The generator of `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂)`. -/
def localGenerator (r : ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r) :=
  (localEquiv r).symm 1

@[simp] theorem localEquiv_localGenerator (r : ℕ) :
    localEquiv r (localGenerator r) = 1 :=
  (localEquiv r).apply_symm_apply 1

theorem localGenerator_ne_zero (r : ℕ) : localGenerator r ≠ 0 := by
  intro h
  have h1 : localEquiv r (localGenerator r) = 1 := localEquiv_localGenerator r
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The local model is one dimensional: every class is a multiple of the
generator. -/
theorem eq_smul_localGenerator (r : ℕ)
    (a : relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) ({(0 : Fin r → ℂ)}ᶜ) (2 * r)) :
    a = (localEquiv r a) • localGenerator r := by
  rw [localGenerator, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

end

end GroupApproximation.CharClass
