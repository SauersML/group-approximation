import GroupApproximation.Higman.OmegaTowerConjugateBasisEdge

/-!
# Signed outer pinches on classified conjugate-basis words

The inner classifier supplies `w : FreeGroup K`.  This file gives the exact
outer Britton collapse for that whole word, for either stable-letter sign.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq HNNExtension

noncomputable def signedCoordShift (m : ℕ) (u : ℤˣ)
    (w : FreeGroup ↥K) : FreeGroup ↥K :=
  if u = 1 then FreeGroup.map (shiftKPowHom m) w
  else FreeGroup.map (unshiftKPowHom m) w

@[simp] theorem signedCoordShift_one (m : ℕ) (w : FreeGroup ↥K) :
    signedCoordShift m 1 w = FreeGroup.map (shiftKPowHom m) w := by
  simp [signedCoordShift]

@[simp] theorem signedCoordShift_negOne (m : ℕ) (w : FreeGroup ↥K) :
    signedCoordShift m (-1) w = FreeGroup.map (unshiftKPowHom m) w := by
  simp [signedCoordShift]

/-- **Exact signed pinch formula for every classified cb-word.** -/
theorem outer_conj_cbHom_signed (m : ℕ) (u : ℤˣ)
    (w : FreeGroup ↥K) :
    (t : SlimOmega m) ^ (u : ℤ) *
        of (slimPiF3Hom m (cbHom w)) *
          ((t : SlimOmega m) ^ (u : ℤ))⁻¹ =
      of (slimPiF3Hom m (cbHom (signedCoordShift m u w))) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · have h := HNNExtension.equiv_eq_conj
      (φ := slimShiftRangeEquiv m)
      ⟨slimPiF3Hom m (cbHom w), ⟨cbHom w, rfl⟩⟩
    have hs := slimShiftRangeEquiv_cbHom m w
    rw [show (((1 : ℤˣ) : ℤ)) = 1 by rfl, zpow_one,
      signedCoordShift_one]
    exact h.symm.trans (congrArg of hs)
  · have h := HNNExtension.equiv_symm_eq_conj
      (φ := slimShiftRangeEquiv m)
      ⟨slimPiF3Hom m (cbHom w), ⟨cbHom w, rfl⟩⟩
    have hs := slimShiftRangeEquiv_symm_cbHom m w
    rw [show (((-1 : ℤˣ) : ℤ)) = -1 by rfl, zpow_neg, zpow_one,
      inv_inv, signedCoordShift_negOne]
    exact h.symm.trans (congrArg of hs)

end Omega
end Higman
end GroupApproximation
