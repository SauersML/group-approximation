import GroupApproximation.Higman.OmegaTowerOuterHull

/-!
# The exact sequence action at an outer Omega pinch

The outer stable letter acts on the associated `F₃` copy by the `m`-fold
shift.  The scan ultimately works with conjugate-basis letters `a_l`, so this
file records the action directly in that vocabulary, without leaving a power
of an abstract automorphism in the pinch formula.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq

/-- The positive outer edge map sends the sequence letter `a_l` to the
literal shifted sequence letter `a_(shiftPow m l)`. -/
theorem slimShiftRangeEquiv_aElt (m : ℕ) (l : E) :
    (((slimShiftRangeEquiv m
        ⟨slimPiF3Hom m (aElt l), ⟨aElt l, rfl⟩⟩ :
          (slimPiF3Hom m).range) : SlimPi m)) =
      slimPiF3Hom m (aElt (shiftPow m l)) := by
  rw [slimShiftRangeEquiv_apply, shiftEquiv_pow_apply,
    shiftAut_iterate_aElt]

/-- Subtype form of the same seam, convenient for applying the inverse edge
equivalence during a negative pinch. -/
theorem slimShiftRangeEquiv_aElt_subtype (m : ℕ) (l : E) :
    slimShiftRangeEquiv m
        ⟨slimPiF3Hom m (aElt l), ⟨aElt l, rfl⟩⟩ =
      ⟨slimPiF3Hom m (aElt (shiftPow m l)),
        ⟨aElt (shiftPow m l), rfl⟩⟩ := by
  apply Subtype.ext
  exact slimShiftRangeEquiv_aElt m l

/-- The negative outer edge map spells the inverse shift as `unshift`. -/
theorem slimShiftRangeEquiv_symm_aElt (m : ℕ) (l : E) :
    ((((slimShiftRangeEquiv m).symm
        ⟨slimPiF3Hom m (aElt l), ⟨aElt l, rfl⟩⟩ :
          (slimPiF3Hom m).range) : SlimPi m)) =
      slimPiF3Hom m (aElt (unshift m l)) := by
  have h := slimShiftRangeEquiv_aElt_subtype m (unshift m l)
  rw [shiftPow_unshift] at h
  have hs := congrArg (slimShiftRangeEquiv m).symm h
  simpa using (congrArg Subtype.val hs).symm

end Omega
end Higman
end GroupApproximation
