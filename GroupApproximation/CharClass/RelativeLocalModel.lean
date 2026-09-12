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
`↥(puncturedSet r)` is `{w // w ≠ 0}` because membership in a singleton complement
unfolds to `≠`, and `Sphere (2d+1)` is the unit sphere of
`EuclideanSpace ℝ (Fin (2*(d+1)))` because `Nat.mul` recurses on its second
argument, so `2*(d+1)` and `(2*d+1)+1` are the same numeral.

The punctured set is given the reducible name `puncturedSet r` rather than
spelled `{(0 : Fin r → ℂ)}ᶜ` at every occurrence: the bare brace notation has no
expected type in a position like `↥(…)` and fails to elaborate there.  Being an
`abbrev` it is reducibly `cc-thom`'s spelling, and `puncturedSet_eq` records that
as an equation.

The case `r = 0` is a genuinely different and easier argument, kept separate: the
punctured space is empty, so the pair collapses by `RelativeLES.relEmptyIso` and
the answer is `H^0` of a one-point space.  `cc-thom` only ever instantiates at
`r ≥ 1`, but the definitions below are total, so no side condition is imposed on
the caller.

## Main definitions

* `localEquiv r : H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂) ≃ₗ[F₂] F₂`.
* `localGenerator r` — the class corresponding to `1`.
* `relCohomologyCongrPoint` — transport along a homeomorphism of the ambient
  subspaces carrying one marked point to the other.

## Main results

* `localGenerator_ne_zero`, `localEquiv_localGenerator`, `eq_smul_localGenerator`.
* `ne_zero_of_iso` — an isomorphism carries a nonzero class to a nonzero class.
* `relCohomologySetCongr` — transport of relative cohomology along an equality of
  subspaces.
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

/-- An isomorphism of `F₂`-modules carries a nonzero class to a nonzero class. -/
theorem ne_zero_of_iso {M N : ModuleCat.{0} (ZMod 2)} (e : M ≅ N) {a : M} (ha : a ≠ 0) :
    e.hom.hom a ≠ 0 := by
  intro h
  refine ha ((ModuleCat.mono_iff_injective e.hom).1 inferInstance ?_)
  rw [h, map_zero]

/-! ## 1. The punctured space and the sphere -/

/-- The complement of the origin in `ℂ^r`.  Reducibly `{(0 : Fin r → ℂ)}ᶜ`. -/
abbrev puncturedSet (r : ℕ) : Set (Fin r → ℂ) := {(0 : Fin r → ℂ)}ᶜ

theorem puncturedSet_eq (r : ℕ) :
    puncturedSet r = ({(0 : Fin r → ℂ)}ᶜ : Set (Fin r → ℂ)) := rfl

theorem one_le_two_mul_succ (d : ℕ) : 1 ≤ 2 * d + 1 := by omega

/-- **`ℂ^{d+1} ∖ 0` is homotopy equivalent to `S^{2d+1}`.**  This is the
fleet-green `AlgTop.complexPuncturedHomotopyEquivSphere`, retyped through the two
definitional identifications described in the module docstring. -/
def puncturedEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(puncturedSet (d + 1)) (Sphere (2 * d + 1)) :=
  AlgTop.complexPuncturedHomotopyEquivSphere d

/-- The cohomology of the punctured space in the sphere's top degree is `F₂`. -/
def puncturedTopEquiv (d : ℕ) :
    Hmod2 (TopCat.of ↥(puncturedSet (d + 1))) (2 * d + 1) ≃ₗ[ZMod 2] ZMod 2 :=
  (pullEquivOfHomotopyEquiv (puncturedEquivSphere d) (2 * d + 1)).symm.trans
    (sphereTopEquiv (2 * d + 1) (one_le_two_mul_succ d))

/-! ## 2. The ambient space is contractible -/

theorem isZero_complexSpace_cohomology (r k : ℕ) (hk : 1 ≤ k) :
    IsZero ((cochainCx (ZMod 2) (TopCat.of (Fin r → ℂ))).homology k) :=
  cohomology_isZero_of_contractible (Fin r → ℂ) k hk

/-! ## 3. The connecting isomorphism of the pair -/

/-- The connecting map of the pair `(ℂ^{d+1}, ℂ^{d+1} ∖ 0)` is an isomorphism in
the relevant degree, both neighbouring absolute groups being zero.  Stated in the
`cochainCx` vocabulary of `relDeltaIso` so that no unfolding is needed here. -/
def puncturedDeltaIso (d : ℕ) :
    (cochainCx (ZMod 2) (TopCat.of (puncturedSet (d + 1)))).homology (2 * d + 1)
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (d + 1) → ℂ))
          (puncturedSet (d + 1)) (2 * (d + 1)) :=
  relDeltaIso (ZMod 2) (TopCat.of (Fin (d + 1) → ℂ)) (puncturedSet (d + 1))
    (2 * d + 1)
    (isZero_complexSpace_cohomology (d + 1) (2 * d + 1) (one_le_two_mul_succ d))
    (isZero_complexSpace_cohomology (d + 1) (2 * d + 1 + 1) (by omega))

/-! ## 4. The degenerate case `r = 0` -/

theorem puncturedSet_zero : puncturedSet 0 = ∅ := by
  ext x
  simp only [puncturedSet, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_not]
  exact funext fun i => i.elim0

/-! ## 5. The local model -/

/-- **(B6)** `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂) ≅ F₂`. -/
def localEquiv : (r : ℕ) →
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r)
      ≃ₗ[ZMod 2] ZMod 2
  | 0 =>
      (relCohomologySetCongr (ZMod 2) (TopCat.of (Fin 0 → ℂ))
          puncturedSet_zero 0).toLinearEquiv.trans
        ((relEmptyIso (ZMod 2) (TopCat.of (Fin 0 → ℂ)) 0).toLinearEquiv.trans
          (cohZeroEquivOfContractible (Fin 0 → ℂ)))
  | (d + 1) =>
      (puncturedDeltaIso d).symm.toLinearEquiv.trans (puncturedTopEquiv d)

/-- **(B6)** The generator of `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂)`. -/
def localGenerator (r : ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r) :=
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
    (a : relCohomology (ZMod 2) (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r)) :
    a = (localEquiv r a) • localGenerator r := by
  rw [localGenerator, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-! ## 6. Transport along a homeomorphism of punctured pairs -/

/-- **The transport `cc-thom` consumes.**  A homeomorphism `e` of the ambient
subspaces `D ⊆ X` and `V ⊆ Y` carrying the marked point `z` to the marked point
`o` induces an isomorphism on the relative cohomology of the punctured pairs.
This is the shape produced by `EulerLocalChart.openPartialHomeomorphChartPair`;
combined with `ne_zero_of_iso` it moves a nonzero local class along a chart with
no degree computation. -/
def relCohomologyCongrPoint {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {D : Set X} {V : Set Y} (e : ↥D ≃ₜ ↥V) {z : X} (hz : z ∈ D) {o : Y} (ho : o ∈ V)
    (hzo : (e ⟨z, hz⟩ : ↥V) = ⟨o, ho⟩) (n : ℕ) :
    relCohomology (ZMod 2) (TopCat.of ↥D)
        ((Subtype.val : ↥D → X) ⁻¹' ({z}ᶜ : Set X)) n
      ≅ relCohomology (ZMod 2) (TopCat.of ↥V)
        ((Subtype.val : ↥V → Y) ⁻¹' ({o}ᶜ : Set Y)) n :=
  relCohomologyCongr e _ _ (by
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

end GroupApproximation.CharClass
