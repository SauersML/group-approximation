import GroupApproximation.CharClass.ThomBridgeChart
import GroupApproximation.CharClass.ThomBridgeHyperplane
import GroupApproximation.CharClass.ThomDataFromLH
import GroupApproximation.CharClass.LerayHirschCompact

/-!
# The Thom bridge, assembled, and the Thom data on the total-space pair

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The Thom data of `CharClass/ThomDataFromLH.lean` lives on the projectivisation
pair `(P(E⊕1), P(E))`.  `cc-lix-odd`'s chain lives on the vector-bundle pair
`(E, E ∖ 0)`.  Both were green and about different objects; the three bridge
steps close that gap, and this file composes them and moves the data across.

```text
H^n(E, E ∖ 0)  ≅  H^n(P(E⊕1), P(E⊕1) ∖ 0)  ≅  H^n(P(E⊕1), P(E))
```

The first isomorphism is `bridgeChart` (excision to the affine chart, then the
chart identified with the total space).  The second is `bridgeHyperplane` with its
input discharged by `hyperplane_hsub`, so it costs a compact Hausdorff base and
nothing else.

Moving the data across is `thomData_transport`, which is pure algebra: an
injective map with a prescribed range, precomposed with an equivalence, is again
injective with the same range.

## Main declarations

* `bridgeTotal` — the composite, as a linear equivalence.
* `thomData_transport` — the algebra.
* `thomData_total_of_lerayHirsch` — **the Thom data on the total-space pair.**
-/

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The composite bridge -/

/-- **The Thom bridge.**  The relative group of the vector-bundle pair is the
relative group of the projectivisation pair, in every degree. -/
def bridgeTotal [CompactSpace X] [T2Space X] (p : Bundle X ι) (n : ℕ) :
    ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n)
      ≃ₗ[ZMod 2] ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Proj p.plusOne))
        (Set.range (Bundle.projIncl p)) n) :=
  LinearEquiv.trans (bridgeChart p n).symm.toLinearEquiv
    (LinearEquiv.ofBijective
      (relPullback (ZMod 2) (𝟙 (TopCat.of (Bundle.Proj p.plusOne)))
        (fun _ hx => range_projIncl_subset_notZero p hx) n).hom
      (bridgeHyperplane p (hyperplane_hsub p) n))

/-! ## 2. Moving the data across an equivalence -/

/-- **An injective map with a prescribed range stays one after precomposition with
an equivalence.**  Nothing here is topology. -/
theorem thomData_transport {A A' N : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup A'] [Module (ZMod 2) A'] [AddCommGroup N] [Module (ZMod 2) N]
    (φ : A ≃ₗ[ZMod 2] A') (jm : A' →ₗ[ZMod 2] N) (hinj : Function.Injective jm)
    {K : Submodule (ZMod 2) N} (hrange : LinearMap.range jm = K) :
    ∃ (jm0 : A →ₗ[ZMod 2] N) (_ : Function.Injective jm0),
      LinearMap.range jm0 = K := by
  refine ⟨jm.comp φ.toLinearMap, hinj.comp φ.injective, ?_⟩
  rw [← hrange]
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨φ.symm b, congrArg jm (φ.apply_symm_apply b)⟩

/-! ## 3. The Thom data where `cc-lix-odd` needs it -/

/-- **The degreewise Thom data of the vector-bundle pair.**  The projectivisation's
data, carried across the bridge.  The two Leray–Hirsch instances and the two
compatibilities are exactly those of `thomData_of_lerayHirsch`; the bridge adds a
compact Hausdorff base and nothing else. -/
theorem thomData_total_of_lerayHirsch [CompactSpace X] [T2Space X] (p : Bundle X ι)
    (π' : TopCat.of (Set.range (Bundle.projIncl p)) ⟶ TopCat.of X)
    (hπ : sInclusion (Set.range (Bundle.projIncl p)) ≫ projMapOf p.plusOne = π')
    (ξ' : Hmod2 (TopCat.of (Set.range (Bundle.projIncl p))) 2)
    (hξ : pull (sInclusion (Set.range (Bundle.projIncl p))) 2
      (tautEulerOf p.plusOne) = ξ')
    {r : ℕ} (hr : 1 ≤ r)
    (L : LerayHirschGraded (projMapOf p.plusOne) (tautEulerOf p.plusOne) (r + 1))
    (L' : LerayHirschGraded π' ξ' r) :
    ∃ (jm : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
          ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
          (2 * r))
        →ₗ[ZMod 2] ((i : Fin (r + 1)) → Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ))))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap (R := ZMod 2)
        (M := fun i : Fin (r + 1) => Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ)))
        (fun i => chernMul L' i)) := by
  obtain ⟨jm, hinj, hrange⟩ :=
    thomData_of_lerayHirsch (X := TopCat.of X)
      (P := TopCat.of (Bundle.Proj p.plusOne)) (r := r)
      (Set.range (Bundle.projIncl p)) (projMapOf p.plusOne)
      π' hπ (tautEulerOf p.plusOne) ξ' hξ hr L L'
  exact thomData_transport (bridgeTotal p (2 * r)) jm hinj hrange

/-! Printed on every build. -/

#print axioms thomData_total_of_lerayHirsch

end ThomChernDeg

end

end GroupApproximation.CharClass
