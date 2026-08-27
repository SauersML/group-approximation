import GroupApproximation.Higman.OmegaTowerConjugateBasisUnshift

/-!
# Both outer Omega edge maps on conjugate-basis words

This connects the positive and inverse word-level naturality lemmas to the
actual associated-subgroup equivalence used by the final HNN extension.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq

theorem shiftEquiv_symm_pow_apply (m : ℕ) (x : F₃) :
    ((shiftEquiv.symm : MulAut F₃) ^ m) x = (shiftAutInv^[m]) x := by
  induction m generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]
      rfl

/-- The inverse of the positive shift power is the iterated inverse shift. -/
theorem shiftEquiv_pow_symm_apply (m : ℕ) (x : F₃) :
    (((shiftEquiv : MulAut F₃) ^ m).symm) x = (shiftAutInv^[m]) x := by
  calc
    (((shiftEquiv : MulAut F₃) ^ m).symm) x =
        ((((shiftEquiv : MulAut F₃) ^ m)⁻¹ : MulAut F₃) x) := rfl
    _ = (((shiftEquiv.symm : MulAut F₃) ^ m) x) := by
      have hpow :
          (((shiftEquiv : MulAut F₃) ^ m)⁻¹ : MulAut F₃) =
            (((shiftEquiv : MulAut F₃)⁻¹) ^ m) :=
        (inv_pow (shiftEquiv : MulAut F₃) m).symm
      exact DFunLike.congr_fun hpow x
    _ = _ := shiftEquiv_symm_pow_apply m x

/-- Positive edge action on an arbitrary conjugate-basis word. -/
theorem slimShiftRangeEquiv_cbHom (m : ℕ) (w : FreeGroup ↥K) :
    (((slimShiftRangeEquiv m
        ⟨slimPiF3Hom m (cbHom w), ⟨cbHom w, rfl⟩⟩ :
          (slimPiF3Hom m).range) : SlimPi m)) =
      slimPiF3Hom m (cbHom (FreeGroup.map (shiftKPowHom m) w)) := by
  rw [slimShiftRangeEquiv_apply, shiftEquiv_pow_cbHom]

/-- Negative edge action on an arbitrary conjugate-basis word. -/
theorem slimShiftRangeEquiv_symm_cbHom (m : ℕ) (w : FreeGroup ↥K) :
    ((((slimShiftRangeEquiv m).symm
        ⟨slimPiF3Hom m (cbHom w), ⟨cbHom w, rfl⟩⟩ :
          (slimPiF3Hom m).range) : SlimPi m)) =
      slimPiF3Hom m (cbHom (FreeGroup.map (unshiftKPowHom m) w)) := by
  have hInv :
      cbHom (FreeGroup.map (unshiftKPowHom m) w) =
        (((shiftEquiv : MulAut F₃) ^ m).symm) (cbHom w) := by
    rw [shiftEquiv_pow_symm_apply, shiftAutInv_iterate_cbHom]
  have h := slimShiftRangeEquiv_cbHom m
    (FreeGroup.map (unshiftKPowHom m) w)
  rw [← shiftEquiv_pow_cbHom, hInv,
    ((shiftEquiv : MulAut F₃) ^ m).apply_symm_apply] at h
  rw [← hInv] at h
  have hrange :
      slimShiftRangeEquiv m
          ⟨slimPiF3Hom m
              (cbHom (FreeGroup.map (unshiftKPowHom m) w)),
            ⟨cbHom (FreeGroup.map (unshiftKPowHom m) w), rfl⟩⟩ =
        ⟨slimPiF3Hom m (cbHom w), ⟨cbHom w, rfl⟩⟩ :=
    Subtype.ext h
  have hs := congrArg (slimShiftRangeEquiv m).symm hrange
  simpa using (congrArg Subtype.val hs).symm

end Omega
end Higman
end GroupApproximation
