import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect

/-!
# The printed defect lies directly in the HS-shadow residual

The proof here follows the displayed proof of
Theorem~`thm:compression-criterion` literally.  Corollary~`cor:defect-hs`
puts every generator indexed by an individual compressor into
`opToHSShadowResidual G`; normality then absorbs their normal closure.

In particular, this module never routes through
`compressionCentralizerDefect` or `compressionGroup`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

variable {G : Type} [Group G]

/-- The generator-by-generator conclusion of `cor:defect-hs`, extended by
normality to the exact defect subgroup printed in the manuscript. -/
theorem printedDefect_le_opToHSShadowResidual (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) :
    printedDefect L ≤ opToHSShadowResidual G := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨compressor, hcompressor, centralizer, hcentralizer,
    ell, hell, rfl⟩
  exact manuscriptCompressionDefectHSInvisible
    G L hL compressor hcompressor centralizer hcentralizer ell hell

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
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      printedDefect L ≤ opToHSShadowResidual G

theorem manuscriptPrintedDefectShadowInclusion :
    PrintedDefectShadowInclusion := by
  intro G _ L hL
  exact printedDefect_le_opToHSShadowResidual L hL

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
