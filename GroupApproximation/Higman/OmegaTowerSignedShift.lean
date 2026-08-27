import GroupApproximation.Higman.OmegaTowerShiftSeam

/-!
# Signed outer-pinch collapse in the Omega tower

An outer Britton pinch carries one of the two units `±1`.  This file turns
that sign into the literal sequence operation performed by the pinch: shift
for `+1`, unshift for `-1`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq HNNExtension

/-- The sequence operation selected by a signed outer edge crossing. -/
noncomputable def signedBlockShift (m : ℕ) (u : ℤˣ) (l : E) : E :=
  if u = 1 then shiftPow m l else unshift m l

@[simp] theorem signedBlockShift_one (m : ℕ) (l : E) :
    signedBlockShift m 1 l = shiftPow m l := by
  simp [signedBlockShift]

@[simp] theorem signedBlockShift_negOne (m : ℕ) (l : E) :
    signedBlockShift m (-1) l = unshift m l := by
  simp [signedBlockShift]

/-- **Exact signed pinch formula.**  Conjugating an embedded conjugate-basis
letter by the outer stable letter with sign `u` returns the conjugate-basis
letter indexed by the corresponding signed block shift. -/
theorem outer_conj_aElt_signed (m : ℕ) (u : ℤˣ) (l : E) :
    (t : SlimOmega m) ^ (u : ℤ) *
        of (slimPiF3Hom m (aElt l)) *
          ((t : SlimOmega m) ^ (u : ℤ))⁻¹ =
      of (slimPiF3Hom m (aElt (signedBlockShift m u l))) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · have h := HNNExtension.equiv_eq_conj
      (φ := slimShiftRangeEquiv m)
      ⟨slimPiF3Hom m (aElt l), ⟨aElt l, rfl⟩⟩
    have hs := slimShiftRangeEquiv_aElt m l
    rw [show (((1 : ℤˣ) : ℤ)) = 1 by rfl, zpow_one,
      signedBlockShift_one]
    exact h.symm.trans (congrArg of hs)
  · have h := HNNExtension.equiv_symm_eq_conj
      (φ := slimShiftRangeEquiv m)
      ⟨slimPiF3Hom m (aElt l), ⟨aElt l, rfl⟩⟩
    have hs := slimShiftRangeEquiv_symm_aElt m l
    rw [show (((-1 : ℤˣ) : ℤ)) = -1 by rfl, zpow_neg, zpow_one,
      inv_inv, signedBlockShift_negOne]
    exact h.symm.trans (congrArg of hs)

end Omega
end Higman
end GroupApproximation
