import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceImageKazhdanRadicalClosure

/-!
# `prop:defect-saturation`, complete and hypothesis-free

`DefectSaturation` in
`GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation` packages
five of the six conclusions printed in Proposition~`prop:defect-saturation`:
functoriality of the defect, absorption of a simple subgroup meeting it,
saturation of the defect from a normally generating simple subgroup, the same
saturation transported along a surjection, and the full MF radical in the
*source* group.

The printed proposition closes with a sixth conclusion, in the image branch:

> If, in addition, `G` is countable and both `L` and `G` have
> property~(T), then `Rad_MF(Q) = Q`.

That conclusion is proved by
`manuscriptImageSaturationFullMFRadicalRoute`, whose printed hypotheses stand
in front of it as ordinary binders.  A theorem with leading binders is exactly
what `#audit_closed_axioms` refuses, so that route is auditable only through
`#audit_axioms`, which reports the axiom closure without certifying that
nothing was assumed.  Folding the hypotheses into the proposition, as
`CompleteOneSidedCompressionCriterion` already does for `thm:compression-criterion`,
puts the sixth clause under the same closed-axiom gate as the other five and
makes one named proposition the complete printed statement.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- **Proposition `prop:defect-saturation` in its complete printed form.**

The first conjunct is the five-clause `DefectSaturation`.  The second is the
image branch's final sentence: with `f` onto, `S ≤ 𝔇_G(L)`, `f(S)` normally
generating `Q`, and with `G` countable and both `L` and `G` Kazhdan, the MF
radical of `Q` is all of `Q`. -/
def CompleteDefectSaturation : Prop :=
  DefectSaturation ∧
    (∀ (G Q : Type) [Group G] [Group Q] [Countable G] (f : G →* Q),
      Function.Surjective f →
      ∀ (L S : Subgroup G),
        HasKazhdanPropertyT.{0, 0} ↥L → HasKazhdanPropertyT.{0, 0} G →
        S ≤ printedDefect L →
        Subgroup.normalClosure (S.map f : Set Q) = ⊤ →
          manuscriptCoronaMFResidual Q = ⊤)

/-- Closed proof of every printed clause of `prop:defect-saturation`. -/
theorem manuscriptCompleteDefectSaturation : CompleteDefectSaturation := by
  refine ⟨manuscriptDefectSaturation, ?_⟩
  intro G Q _ _ _ f hf L S hL hG hSD hgen
  exact (manuscriptImageSaturationFullMFRadicalRoute
    f hf L S hL hG hSD hgen).2.2.2

end OneSidedMFRadical
end Manuscript
end GroupApproximation
