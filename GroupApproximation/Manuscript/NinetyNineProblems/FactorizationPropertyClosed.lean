import GroupApproximation.Manuscript.NinetyNineProblems.KirchbergTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# The factorization-property consequences, with Kirchberg's theorem proved

`Manuscript/NinetyNineProblems/FactorizationProperty.lean` states four consequences of
Kirchberg's Theorem 1.1, each taking the typed input `KirchbergKazhdanFactorizationInput` as its
leading binder `k`.  That input is now inhabited with no assumption
(`KirchbergTheorem.kirchbergKazhdanFactorizationInput`), so this module restates all four
without `k`.

* `not_hasFactorizationProperty_of_simple_infinite_kazhdan_closed`: an infinite simple Kazhdan
  group lacks the factorization property.
* `rankTwelveLeavitt_not_hasFactorizationProperty_closed`: the rank-twelve binary Leavitt
  elementary group `H` lacks it.  Closed.
* `not_forall_sofic_hasFactorizationProperty_of_thom`,
  `not_forall_hyperlinear_hasFactorizationProperty_of_thom`: soficity and hyperlinearity do not
  imply the factorization property.  These keep Thom's construction as the binder
  `t : ThomSoficKazhdanNonResiduallyFiniteInput`, which is not proved here.
-/

namespace GroupApproximation
namespace NinetyNineProblems
namespace FactorizationPropertyClosed

open Manuscript.OneSidedMFRadical

universe u

/-- **An infinite simple Kazhdan group lacks the factorization property**, with Kirchberg's
theorem proved. -/
theorem not_hasFactorizationProperty_of_simple_infinite_kazhdan_closed (G : Type u) [Group G]
    [Countable G] [IsSimpleGroup G] [Infinite G] (hT : HasKazhdanPropertyT.{u, u} G) :
    ¬ HasFactorizationProperty G :=
  not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan
    KirchbergTheorem.kirchbergKazhdanFactorizationInput G hT

/-- **The rank-twelve binary Leavitt elementary group lacks the factorization property.** -/
theorem rankTwelveLeavitt_not_hasFactorizationProperty_closed :
    ¬ HasFactorizationProperty RankTwelveEndpoint.H :=
  rankTwelveLeavitt_not_hasFactorizationProperty
    KirchbergTheorem.kirchbergKazhdanFactorizationInput.{0}

/-- **Soficity does not imply the factorization property**, from Thom's examples. -/
theorem not_forall_sofic_hasFactorizationProperty_of_thom
    (t : ThomSoficKazhdanNonResiduallyFiniteInput.{u}) :
    ¬ ∀ (G : Type u) [Group G] [Countable G], IsSofic G → HasFactorizationProperty G :=
  not_forall_sofic_hasFactorizationProperty
    KirchbergTheorem.kirchbergKazhdanFactorizationInput t

/-- **Hyperlinearity does not imply the factorization property**, from Thom's examples. -/
theorem not_forall_hyperlinear_hasFactorizationProperty_of_thom
    (t : ThomSoficKazhdanNonResiduallyFiniteInput.{u}) :
    ¬ ∀ (G : Type u) [Group G] [Countable G], IsHyperlinear G → HasFactorizationProperty G :=
  not_forall_hyperlinear_hasFactorizationProperty
    KirchbergTheorem.kirchbergKazhdanFactorizationInput t

end FactorizationPropertyClosed
end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems.FactorizationPropertyClosed

#audit_closed_axioms rankTwelveLeavitt_not_hasFactorizationProperty_closed
#audit_axioms not_hasFactorizationProperty_of_simple_infinite_kazhdan_closed
#audit_axioms not_forall_sofic_hasFactorizationProperty_of_thom
#audit_axioms not_forall_hyperlinear_hasFactorizationProperty_of_thom
