import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual

/-!
# The printed defect lies directly in the HS-shadow residual

The generic shadow-residual module identifies the printed ordinary-limit
residual with the development's ultrafilter definition and proves the exact
printed-defect inclusion.  This module reuses that inclusion and composes it
with the normal-Kazhdan theorem, rather than maintaining a second proof of the
same subgroup inequality.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

variable {G : Type} [Group G]

/-- The first clause of the one-sided compression criterion, now derived
along the manuscript's direct route: printed generators, HS-shadow normality,
then the normal-Kazhdan radical theorem. -/
theorem normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect
    [Countable G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (K : Subgroup G) [K.Normal]
    (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKD : K ≤ printedDefect L) :
    K ≤ actualCoronaMFResidual G :=
  manuscriptNormalKazhdanRadical G (printedDefect L)
    (printedDefect_le_opToHSShadowResidual L hL) K hK hKD

/-! ## Closed endpoints for the manuscript audit -/

/-- The exact printed-defect shadow inclusion as a closed proposition. -/
def PrintedDefectShadowInclusion : Prop :=
  PrintedDefectLeShadowResidual

theorem manuscriptPrintedDefectShadowInclusion :
    PrintedDefectShadowInclusion :=
  manuscriptPrintedDefectLeShadowResidual

/-- The normal-Kazhdan clause on the exact printed defect, packaged for the
closed-axiom audit. -/
def PrintedDefectNormalKazhdanRadical : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (K : Subgroup G) [K.Normal],
        HasKazhdanPropertyT.{0, 0} ↥K → K ≤ printedDefect L →
          K ≤ actualCoronaMFResidual G

theorem manuscriptPrintedDefectNormalKazhdanRadical :
    PrintedDefectNormalKazhdanRadical := by
  intro G _ _ L hL K _ hK hKD
  exact normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect
    L hL K hK hKD

end OneSidedMFRadical
end Manuscript
end GroupApproximation
