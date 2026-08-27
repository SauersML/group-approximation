import GroupApproximation.Domination.PresentationRadical
import GroupApproximation.Sofic.LEFSofic
import Mathlib.GroupTheory.Finiteness

/-!
# Residually finite detectors for presentation radicals

This file isolates the algebraic detector used by fixed-dimensional arguments.
If a homomorphism into a residually finite image detects the marked word, then
that word cannot belong to the sofic radical of the presentation.

The separate finite-generation lemma records the other algebraic input needed
when Mal'cev's theorem is used to establish residual finiteness of a linear
image.
-/

namespace GroupApproximation

/-- A detector into a residually finite image contradicts membership in the
sofic radical.  Residually finite groups are sofic through the classical
chain `residually finite → LEF → sofic`. -/
theorem not_soficPresentationInvisible_of_residuallyFinite_detector
    {α : Type} {R : Finset (FreeGroup α)} {w : FreeGroup α}
    {H : Type} [Group H]
    (ρ : PresentedGroup (R : Set (FreeGroup α)) →* H)
    [Group.ResiduallyFinite ρ.range]
    (hdetect : ρ (PresentedGroup.mk (R : Set (FreeGroup α)) w) ≠ 1) :
    ¬ SoficPresentationInvisible R w := by
  intro hw
  have hkilled : ρ.rangeRestrict
      (PresentedGroup.mk (R : Set (FreeGroup α)) w) = 1 :=
    hw ρ.range inferInstance
      (isSofic_of_isLEF isLEF_of_residuallyFinite) ρ.rangeRestrict
  apply hdetect
  simpa using congrArg Subtype.val hkilled

/-- The image of a finite presentation under any homomorphism is finitely
generated.  This is the finite-generation input to Mal'cev's theorem. -/
theorem finitePresentationDetector_range_fg
    {α : Type} [Finite α] {R : Finset (FreeGroup α)}
    {H : Type} [Group H]
    (ρ : PresentedGroup (R : Set (FreeGroup α)) →* H) :
    Group.FG ρ.range := by
  letI : Group.FG (PresentedGroup (R : Set (FreeGroup α))) :=
    Group.fg_of_surjective
      (PresentedGroup.mk_surjective (R : Set (FreeGroup α)))
  infer_instance

end GroupApproximation
