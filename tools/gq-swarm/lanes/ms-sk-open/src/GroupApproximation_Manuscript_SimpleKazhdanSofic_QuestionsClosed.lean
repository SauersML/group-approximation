import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsNotFinitelyPresented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The embedded claims of "Questions", closed

`simple_kazhdan_sofic_group.tex` at census 9cb80166d (tip 8b36733d7), section "Questions":

> Infinite finitely presented simple Kazhdan groups exist [CapraceRemy], while `G_X` is not finitely
> presented: a finitely presented LEF group is residually finite [Stepin, VershikGordon], and `G_X` is
> not.  A sofic example would not be LEF, and it would also answer Open problem 6.1 of Alekseev and
> Thom [AlekseevThom], which asks for finitely presented sofic groups with property (T) that are not
> residually finite.

The ingredients are ct-involution's `QuestionsNotFinitelyPresented`:
* `printedFinitelyPresentedLEFResiduallyFinite`;
* `printedNotFinitelyPresentedOfLEFSimpleInfinite`;
* `printedGXNotFinitelyPresented_of_main`, over `PrintedSimpleKazhdanSoficMain`.

This module adds two endpoints.

* `printedGXNotFinitelyPresented`: `G_X` is not finitely presented, for every infinite minimal subshift.
  It discharges the instance with the closed `printedSimpleKazhdanSoficMain`.
* `printedSoficKazhdanExampleNotLEF`: an infinite, finitely presented, simple, sofic Kazhdan group is
  not LEF, and it is a finitely presented sofic group with property (T) that is not residually finite.
  The reason is the printed one: a finitely presented LEF group is residually finite, and an infinite
  simple group is not.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- **`G_X` is not finitely presented**, for every infinite minimal subshift `X` over a finite
alphabet. -/
theorem printedGXNotFinitelyPresented : PrintedGXNotFinitelyPresented :=
  printedGXNotFinitelyPresented_of_main printedSimpleKazhdanSoficMain

/-- **A sofic example would not be LEF, and would answer Alekseev–Thom 6.1.**  An infinite, finitely
presented, simple, sofic group with property (T) is not LEF, and it is a finitely presented sofic
group with property (T) that is not residually finite. -/
def PrintedSoficKazhdanExampleNotLEF : Prop :=
  ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G], Group.IsFinitelyPresented G →
    HasKazhdanPropertyT.{0, 0} G → IsSofic G →
      ¬ IsLEF G ∧ (Group.IsFinitelyPresented G ∧ IsSofic G ∧ HasKazhdanPropertyT.{0, 0} G ∧
        ¬ IsResiduallyFinite G)

theorem printedSoficKazhdanExampleNotLEF : PrintedSoficKazhdanExampleNotLEF := by
  intro G _ _ _ hfp hT hsof
  exact ⟨fun hLEF => printedNotFinitelyPresentedOfLEFSimpleInfinite G hLEF hfp, hfp, hsof, hT,
    NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite G⟩

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedGXNotFinitelyPresented
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedSoficKazhdanExampleNotLEF
