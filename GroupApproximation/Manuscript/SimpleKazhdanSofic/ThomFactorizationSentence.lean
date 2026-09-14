import GroupApproximation.Manuscript.NinetyNineProblems.KirchbergTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Thom's example and the factorization property

`simple_kazhdan_sofic_group.tex` at f34e9c0b1, tex l.93–95:

> Thom constructed a finitely generated Kazhdan LEF group that is not residually finite and so
> lacks the factorization property [Thom], but his example is not simple.

The sentence cites Thom's construction and asserts one inference: a Kazhdan group that is not
residually finite lacks the factorization property.  That is the contrapositive of Kirchberg's
Theorem 1.1, proved in `Manuscript/NinetyNineProblems/KirchbergTheorem` with no input, and it is
carried here as `printedKazhdanNotResiduallyFiniteLacksFactorizationProperty` for every group.

Thom's group itself (finitely generated, Kazhdan, LEF, not residually finite, not simple) is
credit.  No later step of the note uses it, and it is not proved here; it remains the typed input
`NinetyNineProblems.ThomSoficKazhdanNonResiduallyFiniteInput`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open NinetyNineProblems

universe u

/-- **"not residually finite and so lacks the factorization property"** (tex l.93–95): a Kazhdan
group that is not residually finite lacks the factorization property. -/
def PrintedKazhdanNotResiduallyFiniteLacksFactorizationProperty : Prop :=
  ∀ (G : Type u) [Group G], HasKazhdanPropertyT.{u, u} G → ¬ IsResiduallyFinite G →
    ¬ HasFactorizationProperty G

theorem printedKazhdanNotResiduallyFiniteLacksFactorizationProperty :
    PrintedKazhdanNotResiduallyFiniteLacksFactorizationProperty.{u} :=
  fun G _ hT hnrf hfp ↦ hnrf (KirchbergTheorem.printedKirchbergTheorem G hT hfp)

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedKazhdanNotResiduallyFiniteLacksFactorizationProperty
