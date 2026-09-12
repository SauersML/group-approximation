import GroupApproximation.CharClass.RelativeLocalModel
import GroupApproximation.CharClass.KroneckerSphere
import GroupApproximation.Meta.AxiomGuard

/-!
# The local model `H^{2r}(ℂ^r, ℂ^r ∖ 0; K) ≅ K`, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4 and §1.5).

Additive twin of `RelativeLocalModel.lean` with the coefficients a field `K`.  The route is the
`F₂` file's, every input replaced by its `K`-coefficient version:

* `ℂ^r` is contractible, so its cohomology vanishes in positive degrees
  (`KroneckerContractible.cohomology_isZero_of_contractibleOf`);
* so the connecting map of the pair is an isomorphism
  `H^{2d+1}(ℂ^{d+1} ∖ 0; K) ≅ H^{2d+2}(ℂ^{d+1}, ℂ^{d+1} ∖ 0; K)` (`RelativeLES.relDeltaIso`,
  already generic);
* `ℂ^{d+1} ∖ 0` is homotopy equivalent to `S^{2d+1}` (`RelativeLocalModel.puncturedEquivSphere`,
  no coefficients) and homotopy invariance holds over any ring
  (`KroneckerContractible.pullEquivOfHomotopyEquivOf`);
* `H^{2d+1}(S^{2d+1}; K) ≅ K` (`KroneckerSphere.sphereTopEquivOf`).

Degree `r = 0` collapses by `relEmptyIso` to `H^0` of a point, `cohZeroEquivOfContractibleOf`.

**What changes at odd `p`.**  Over `F₂` a line has exactly one nonzero element, which is how the
mod-2 Step C identifies a local class with *the* generator.  Over `K` a nonzero class is a
**unit multiple** of the generator (`eq_smul_localGeneratorOf`, `isUnit_localEquivOf_of_ne_zero`),
and a count that only needs `c ≠ 0` (`LIXKCount.map_ne_zero_of_localSplit`) never needs more.
`localEquivOf` is not definitionally `localEquiv` at `K = ZMod 2`: the sphere isomorphism over `K`
is chosen by a rank argument, so the two generators agree only as the one nonzero element.

## Main definitions

* `localEquivOf K r : H^{2r}(ℂ^r, ℂ^r ∖ 0; K) ≃ₗ[K] K`, `localGeneratorOf K r`.
* `relCohomologyCongrPointOf` — transport along a homeomorphism carrying one marked point to
  another, over any ring.

## Main results

* `localGeneratorOf_ne_zero`, `eq_smul_localGeneratorOf`, `isUnit_localEquivOf_of_ne_zero`.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- An isomorphism of `K`-modules carries a nonzero element to a nonzero element. -/
theorem ne_zero_of_isoOf {K : Type} [CommRing K] {M N : ModuleCat.{0} K} (e : M ≅ N) {a : M}
    (ha : a ≠ 0) : e.hom.hom a ≠ 0 := by
  intro h
  refine ha ((ModuleCat.mono_iff_injective e.hom).1 inferInstance ?_)
  rw [h, map_zero]

/-! ## 1. The punctured space in the sphere's top degree -/

/-- The cohomology of the punctured space in the sphere's top degree is `K`. -/
def puncturedTopEquivOf (K : Type) [Field K] (d : ℕ) :
    Hmod K (TopCat.of ↥(puncturedSet (d + 1))) (2 * d + 1) ≃ₗ[K] K :=
  (pullEquivOfHomotopyEquivOf K (puncturedEquivSphere d) (2 * d + 1)).symm.trans
    (sphereTopEquivOf K (2 * d + 1) (one_le_two_mul_succ d))

/-! ## 2. The ambient space is contractible -/

theorem isZero_complexSpace_cohomologyOf (K : Type) [Field K] (r k : ℕ) (hk : 1 ≤ k) :
    IsZero ((cochainCx K (TopCat.of (Fin r → ℂ))).homology k) :=
  cohomology_isZero_of_contractibleOf K (Fin r → ℂ) k hk

/-! ## 3. The connecting isomorphism of the pair -/

/-- The connecting map of the pair `(ℂ^{d+1}, ℂ^{d+1} ∖ 0)` is an isomorphism in the relevant
degree, over `K`. -/
def puncturedDeltaIsoOf (K : Type) [Field K] (d : ℕ) :
    (cochainCx K (TopCat.of (puncturedSet (d + 1)))).homology (2 * d + 1)
      ≅ relCohomology K (TopCat.of (Fin (d + 1) → ℂ)) (puncturedSet (d + 1)) (2 * (d + 1)) :=
  relDeltaIso K (TopCat.of (Fin (d + 1) → ℂ)) (puncturedSet (d + 1)) (2 * d + 1)
    (isZero_complexSpace_cohomologyOf K (d + 1) (2 * d + 1) (one_le_two_mul_succ d))
    (isZero_complexSpace_cohomologyOf K (d + 1) (2 * d + 1 + 1) (by omega))

/-! ## 4. The local model -/

/-- `H^{2r}(ℂ^r, ℂ^r ∖ 0; K) ≅ K`. -/
def localEquivOf (K : Type) [Field K] : (r : ℕ) →
    relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r) ≃ₗ[K] K
  | 0 =>
      (relCohomologySetCongr K (TopCat.of (Fin 0 → ℂ)) puncturedSet_zero 0).toLinearEquiv.trans
        ((relEmptyIso K (TopCat.of (Fin 0 → ℂ)) 0).toLinearEquiv.trans
          (cohZeroEquivOfContractibleOf K (Fin 0 → ℂ)))
  | (d + 1) =>
      (puncturedDeltaIsoOf K d).symm.toLinearEquiv.trans (puncturedTopEquivOf K d)

/-- The generator of `H^{2r}(ℂ^r, ℂ^r ∖ 0; K)`. -/
def localGeneratorOf (K : Type) [Field K] (r : ℕ) :
    relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r) :=
  (localEquivOf K r).symm 1

@[simp] theorem localEquivOf_localGeneratorOf (K : Type) [Field K] (r : ℕ) :
    localEquivOf K r (localGeneratorOf K r) = 1 :=
  (localEquivOf K r).apply_symm_apply 1

theorem localGeneratorOf_ne_zero (K : Type) [Field K] (r : ℕ) : localGeneratorOf K r ≠ 0 := by
  intro h
  have h1 : localEquivOf K r (localGeneratorOf K r) = 1 := localEquivOf_localGeneratorOf K r
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The local model is one dimensional: every class is a multiple of the generator. -/
theorem eq_smul_localGeneratorOf (K : Type) [Field K] (r : ℕ)
    (a : relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r)) :
    a = (localEquivOf K r a) • localGeneratorOf K r := by
  rw [localGeneratorOf, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-- A nonzero class of the local model is a **unit** multiple of the generator. -/
theorem isUnit_localEquivOf_of_ne_zero (K : Type) [Field K] (r : ℕ)
    {a : relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r)} (ha : a ≠ 0) :
    IsUnit (localEquivOf K r a) := by
  refine isUnit_iff_ne_zero.2 ?_
  intro h
  refine ha ?_
  rw [eq_smul_localGeneratorOf K r a, h, zero_smul]

/-! ## 5. Transport along a homeomorphism of punctured pairs -/

/-- A homeomorphism `e` of the ambient subspaces `D ⊆ X` and `V ⊆ Y` carrying the marked point
`z` to the marked point `o` induces an isomorphism on the relative cohomology of the punctured
pairs, over any commutative ring. -/
def relCohomologyCongrPointOf (K : Type) [CommRing K] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {D : Set X} {V : Set Y} (e : ↥D ≃ₜ ↥V) {z : X} (hz : z ∈ D) {o : Y}
    (ho : o ∈ V) (hzo : (e ⟨z, hz⟩ : ↥V) = ⟨o, ho⟩) (n : ℕ) :
    relCohomology K (TopCat.of ↥D) ((Subtype.val : ↥D → X) ⁻¹' ({z}ᶜ : Set X)) n
      ≅ relCohomology K (TopCat.of ↥V) ((Subtype.val : ↥V → Y) ⁻¹' ({o}ᶜ : Set Y)) n :=
  relCohomologyCongrOf K e _ _ (by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      intro hcon
      refine hq ?_
      have h1 : e q = ⟨o, ho⟩ := Subtype.ext hcon
      have h2 : q = ⟨z, hz⟩ := by
        apply e.injective
        rw [h1, hzo]
      exact congrArg Subtype.val h2
    · intro hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      intro hcon
      refine hp ?_
      have h1 : e.symm p = ⟨z, hz⟩ := Subtype.ext hcon
      have h2 : p = ⟨o, ho⟩ := by
        rw [← e.apply_symm_apply p, h1, hzo]
      exact congrArg Subtype.val h2) n

end

/-! Audited on every build. -/

#audit_axioms localGeneratorOf_ne_zero
#audit_axioms eq_smul_localGeneratorOf
#audit_axioms isUnit_localEquivOf_of_ne_zero

end GroupApproximation.CharClass
