import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Sofic.ContinuumMultiplicityCore
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Factorization
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Kirchberg.Theorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ProductExample
import GroupApproximation.Meta.AxiomGuard

/-!
# Row A2 endpoints: Ozawa, Kirchberg/Thom

Source: `simple_kazhdan_sofic_group.tex`, table row A2.

* tex l.57-59 (Kirchberg; Thom, GGD 4 (2010)): a Kazhdan group that is not residually finite
  does not have the factorization property.
  `not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite`, from lane A2Kirchberg's
  `isResiduallyFinite_of_hasKazhdanPropertyT_of_hasFactorizationProperty`.
* The same sentence realised by a witness: `exists_fg_kazhdan_lef_not_rf_not_fp_not_simple`
  (G_X x G_X at the Toeplitz subshift, from `ProductExample`).
* tex l.54-56 (Ozawa): the full C*-algebra of an infinite simple Kazhdan hyperlinear group does not
  have the local lifting property. `ozawa_not_hasLocalLiftingProperty`, from Kirchberg plus lane
  A2LocalLifting's `not_hasLocalLiftingProperty_of_not_hasFactorizationProperty`.
* tex l.60 (Thom's example is not simple) is `not_isSimpleGroup_thomGroup_zmod` in `ThomGroup`.
-/

namespace GroupApproximation.Full.A2Endpoint

open GroupApproximation.NinetyNineProblems

/-- tex l.57-59 (Kirchberg, Thom): Kazhdan and not residually finite implies no factorization
property. -/
theorem not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite {G : Type} [Group G]
    (hT : HasKazhdanPropertyT.{0, 0} G) (hnrf : ¬ IsResiduallyFinite G) :
    ¬ HasFactorizationProperty G := fun hF ↦
  hnrf (A2Kirchberg.isResiduallyFinite_of_hasKazhdanPropertyT_of_hasFactorizationProperty hT hF)

/-- tex l.57-60, witnessed: a finitely generated Kazhdan LEF group that is not residually finite,
has no factorization property, and is not simple. -/
theorem exists_fg_kazhdan_lef_not_rf_not_fp_not_simple :
    ∃ (E : Type) (_ : Group E), Group.FG E ∧ HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E ∧
      ¬ IsResiduallyFinite E ∧ ¬ HasFactorizationProperty E ∧ ¬ IsSimpleGroup E := by
  obtain ⟨E, hE, hfg, hT, hlef, hnrf, hns⟩ := exists_fg_kazhdan_lef_not_residuallyFinite_not_simple
  exact ⟨E, hE, hfg, hT, hlef, hnrf,
    not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite hT hnrf, hns⟩

/-- tex l.54-56 (Ozawa): the full group C*-algebra of an infinite simple Kazhdan hyperlinear
group does not have the local lifting property. -/
theorem ozawa_not_hasLocalLiftingProperty (G : Type) [Group G] [IsSimpleGroup G] [Infinite G]
    (hT : HasKazhdanPropertyT.{0, 0} G) (hH : IsHyperlinear G) :
    ¬ A2LocalLifting.HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G) := by
  haveI : Group.FG G := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT G hT
  haveI : Countable G := ContinuumMultiplicity.countable_of_fg G
  exact A2LocalLifting.not_hasLocalLiftingProperty_of_not_hasFactorizationProperty G hH
    (A2Kirchberg.not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan G hT)

#audit_axioms GroupApproximation.Full.A2Endpoint.not_hasFactorizationProperty_of_kazhdan_of_not_residuallyFinite
#audit_axioms GroupApproximation.Full.A2Endpoint.exists_fg_kazhdan_lef_not_rf_not_fp_not_simple
#audit_axioms GroupApproximation.Full.A2Endpoint.ozawa_not_hasLocalLiftingProperty

end GroupApproximation.Full.A2Endpoint
