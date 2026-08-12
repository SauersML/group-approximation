import GroupApproximation.Domination.PresentationRadical
import GroupApproximation.Sofic.LEFSofic
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The algebraic finite-jet contradiction

This file isolates the algebraic end of the fixed-dimensional arc argument.
Once truncation produces an exact representation of the presented group in a
finite-dimensional coefficient algebra and the marked word survives, the
word cannot belong to the sofic radical.

The external theorem which supplies residual finiteness is Mal'cev's theorem:
every finitely generated linear group over a field is residually finite.  We
do not rebrand that classical theorem as part of the contribution.  The first
endpoint below is stated at exactly the interface Mal'cev supplies, while the
analytic file is responsible only for manufacturing the finite jet.
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
