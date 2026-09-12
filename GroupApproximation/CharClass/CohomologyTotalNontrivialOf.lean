import GroupApproximation.CharClass.CohomologyTotalNontrivial
import GroupApproximation.CharClass.ChernTotalRingOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The cohomology ring of a nonempty space over a nontrivial ring is nontrivial

Lane `lix-cupone`: the coefficient-generic twin of `CohomologyDegreeZero.one_ne_zero_cohZero` and
`CohomologyTotalNontrivial.nontrivial_totalH`, for lix-lh's odd-primary Chern layer.  The `F₂` names
are unchanged.

In degree `0` the differential into the cochains has no source, so `homologyπ` is an isomorphism and
the class map is injective there.  The unit cochain takes the value `1` on the `0`-simplex at a point,
so the unit class is nonzero as soon as the space has a point and `1 ≠ 0` in `K`.  In the total ring
`1` is that class placed in degree `0`.

## Main declarations

* `cocycleClassK_zero_injectiveOf` — injectivity of the class map in degree `0`.
* `one_ne_zero_cohZeroOf` — the unit class is nonzero.
* `nontrivial_totalHOf` — **the ring is nontrivial**, with the instance form.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **In degree zero the class map is injective**, over any ring. -/
theorem cocycleClassK_zero_injectiveOf (K : Type) [CommRing K] (X : TopCat.{0})
    (φ : singularCochainGroup K X 0) (hφ : cochainCoboundary K X 0 φ = 0)
    (h : cocycleClassK K X 0 φ hφ = 0) : φ = 0 := by
  haveI : IsIso ((cochainCxK K X).homologyπ 0) :=
    (cochainCxK K X).isIso_homologyπ 0 0 (by simp [ComplexShape.prev])
      ((cochainCxK K X).shape 0 0 (by simp))
  have hinj : Function.Injective ((cochainCxK K X).homologyπ 0).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hcyc : (cochainCxK K X).cyclesMk φ (0 + 1) (ComplexShape.next_eq' _ rfl) hφ = 0 :=
    hinj (by rw [map_zero]; exact h)
  have h2 := iCycles_cyclesMkK K X 0 φ hφ
  rw [hcyc, map_zero] at h2
  exact h2.symm

/-- **The unit class is nonzero** for a nonempty space over a nontrivial ring. -/
theorem one_ne_zero_cohZeroOf (K : Type) [CommRing K] [Nontrivial K] (X : TopCat.{0})
    [Nonempty X] : one (K := K) X ≠ (0 : Hmod K X 0) := by
  intro h
  rw [one_eq_cocycleClassOf K X] at h
  have h0 := cocycleClassK_zero_injectiveOf K X _ (cochainCoboundary_cochainOneK K X) h
  have hev : cochainEval 0 (cochainOne (R := K) (Z := X))
      (pointSimplex X (Classical.arbitrary X)) = 0 := by
    rw [h0]
    exact cochainEval_zero 0 _
  rw [cochainOne_eval] at hev
  exact one_ne_zero hev

/-- **The cohomology ring of a nonempty space over a nontrivial ring is nontrivial.** -/
theorem nontrivial_totalHOf (K : Type) [CommRing K] [Nontrivial K] (X : TopCat.{0})
    [Nonempty X] : Nontrivial (TotalHOf K X) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  rw [← TotalHOf.of_one K X] at h
  exact one_ne_zero_cohZeroOf K X ((TotalHOf.of_eq_zero_iff K X 0 (one (K := K) X)).mp h)

/-- The instance form. -/
instance nontrivial_totalHOf_inst (K : Type) [CommRing K] [Nontrivial K] (X : TopCat.{0})
    [Nonempty X] : Nontrivial (TotalHOf K X) :=
  nontrivial_totalHOf K X

/-- Over every nontrivial commutative ring, the cohomology ring of a nonempty space is
nontrivial. -/
def PrintedCohomologyTotalNontrivial : Prop :=
  ∀ (K : Type) [CommRing K] [Nontrivial K] (X : TopCat.{0}) [Nonempty X], Nontrivial (TotalHOf K X)

theorem printedCohomologyTotalNontrivial : PrintedCohomologyTotalNontrivial := by
  intro K _ _ X _
  exact nontrivial_totalHOf K X

#audit_closed_axioms printedCohomologyTotalNontrivial

end

end GroupApproximation.CharClass
