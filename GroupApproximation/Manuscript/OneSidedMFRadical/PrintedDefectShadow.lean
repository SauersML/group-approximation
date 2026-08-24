import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual

/-!
# The printed defect lies directly in the HS-shadow residual

The generic shadow-residual module identifies the printed ordinary-limit
residual with the development's ultrafilter definition and supplies its
normality.  The manuscript-facing inclusion below deliberately follows the
printed proof generator by generator: `manuscriptCompressionDefectHSInvisible`
kills each displayed commutator, and normality absorbs their normal closure.
It does not route through the larger defect indexed by `compressionGroup`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

variable {G : Type} [Group G]

/-- The exact printed defect lies in the shadow residual, proved directly
from the displayed generator calculation and normality.  This proof never
enlarges `printedDefect` to `compressionCentralizerDefect`. -/
theorem printedDefect_le_opToHSShadowResidual_direct
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} ↥L) :
    printedDefect L ≤ opToHSShadowResidual G := by
  letI : (opToHSShadowResidual G).Normal :=
    (manuscriptShadowResidualIsNormal G).1
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨u, hu, c, hc, ell, hell, rfl⟩
  exact manuscriptCompressionDefectHSInvisible G L hL u hu c hc ell hell

/-- The first clause of the one-sided compression criterion, now derived
along the manuscript's direct route: printed generators, HS-shadow normality,
then the normal-Kazhdan radical theorem. -/
theorem normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect
    [Countable G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (K : Subgroup G) [K.Normal]
    (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKD : K ≤ printedDefect L) :
    K ≤ actualCoronaMFResidual G := by
  have hshadow : printedDefect L ≤ opToHSShadowResidual G :=
    printedDefect_le_opToHSShadowResidual_direct L hL
  exact manuscriptNormalKazhdanRadical G (printedDefect L)
    hshadow K hK hKD

/-! ## Closed endpoints for the manuscript audit -/

/-- The exact printed-defect shadow inclusion as a closed proposition. -/
def PrintedDefectShadowInclusion : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      printedDefect L ≤ opToHSShadowResidual G

theorem manuscriptPrintedDefectShadowInclusion :
    PrintedDefectShadowInclusion := by
  intro G _ L hL
  exact printedDefect_le_opToHSShadowResidual_direct L hL

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
