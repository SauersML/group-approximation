import GroupApproximation.Manuscript.NinetyNineProblems.KirchbergTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Kirchberg's theorem and the factorization property in "Brown's formulation"

`simple_kazhdan_sofic_group.tex`, section "Brown's formulation" (tex l.283–290 at 696c4b602):

> Kirchberg proved that a Kazhdan group with the factorization property is residually
> finite [Theorem 1.1], and that every subgroup of the unitary group of `𝓡` has the
> factorization property [Corollary 1.2]. So `G` does not have the factorization property,
> it is not a subgroup of the unitary group of `𝓡`, and `C*(G)` does not have the local
> lifting property [p. 527].

This module carries the first clause of each sentence.

* `printedKirchbergTheoremOneOne`: Theorem 1.1, proved in
  `Manuscript/NinetyNineProblems/KirchbergTheorem` with no input.  The factorization property
  is the repository's trace-side definition `HasFactorizationProperty`, which is Ozawa's
  (F) (Def. 7.2 via Thm. 6.1 (ii)).
* `printedGLacksFactorizationProperty`: "So `G` does not have the factorization property".
  The sentence uses that `G` is infinite, simple and Kazhdan.  An infinite simple group is not
  residually finite (`not_isResiduallyFinite_of_isSimpleGroup_of_infinite`), so Theorem 1.1
  excludes the factorization property.  No countability is needed.

Corollary 1.2, "`G` is not a subgroup of the unitary group of `𝓡`", and the LLP clause are
not carried here.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open NinetyNineProblems

universe u

/-- **Kirchberg's Theorem 1.1** (tex l.283–285): a Kazhdan group with the factorization
property is residually finite. -/
def PrintedKirchbergTheoremOneOne : Prop :=
  ∀ (G : Type u) [Group G], HasKazhdanPropertyT.{u, u} G → HasFactorizationProperty G →
    IsResiduallyFinite G

theorem printedKirchbergTheoremOneOne : PrintedKirchbergTheoremOneOne.{u} :=
  KirchbergTheorem.printedKirchbergTheorem

/-- **"So `G` does not have the factorization property"** (tex l.287–288), for the infinite
simple Kazhdan groups of Theorem `thm:general`. -/
def PrintedGLacksFactorizationProperty : Prop :=
  ∀ (G : Type u) [Group G] [IsSimpleGroup G] [Infinite G],
    HasKazhdanPropertyT.{u, u} G → ¬ HasFactorizationProperty G

theorem printedGLacksFactorizationProperty : PrintedGLacksFactorizationProperty.{u} :=
  fun G _ _ _ hT hfp ↦
    not_isResiduallyFinite_of_isSimpleGroup_of_infinite G
      (printedKirchbergTheoremOneOne G hT hfp)

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedKirchbergTheoremOneOne
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGLacksFactorizationProperty
