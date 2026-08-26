import GroupApproximation.Higman.OmegaTowerStageTwo

/-!
# The third stage of the omega tower

This module builds the final mapping-torus stage from the precise remaining
Britton obligation at stage two: injectivity of `slimPiF3Hom`.  It transports
the `m`-fold shift to the embedded copy of `F₃`, forms the actual HNN
extension, proves that `F₃` still embeds, and proves the stable-letter
conjugation formula required by `Omega.Tower`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- The `m`-fold shift transported to the stage-two copy of `F₃`. -/
noncomputable def slimShiftRangeEquiv (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) :
    (slimPiF3Hom m).range ≃* (slimPiF3Hom m).range :=
  ((MonoidHom.ofInjective hemb).symm.trans
    ((shiftEquiv : MulAut F₃) ^ m)).trans (MonoidHom.ofInjective hemb)

theorem shiftEquiv_pow_apply (m : ℕ) (x : F₃) :
    ((shiftEquiv : MulAut F₃) ^ m) x = (⇑shiftAut)^[m] x := by
  induction m generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]
      rfl

theorem slimShiftRangeEquiv_apply (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) (x : F₃) :
    ((slimShiftRangeEquiv m hemb
        ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩ : (slimPiF3Hom m).range) : SlimPi m) =
      slimPiF3Hom m (((shiftEquiv : MulAut F₃) ^ m) x) := by
  have hx : (MonoidHom.ofInjective hemb).symm
      ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩ = x := by
    apply (MonoidHom.ofInjective hemb).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  change slimPiF3Hom m (((shiftEquiv : MulAut F₃) ^ m)
      ((MonoidHom.ofInjective hemb).symm ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩)) = _
  rw [hx]

/-- The slim third stage, an HNN extension of stage two along the transported
`m`-fold shift. -/
abbrev SlimOmega (m : ℕ) (hemb : Function.Injective (slimPiF3Hom m)) : Type :=
  HNNExtension (SlimPi m) (slimPiF3Hom m).range (slimPiF3Hom m).range
    (slimShiftRangeEquiv m hemb)

/-- The stage-two base inside the final slim tower. -/
noncomputable def slimOmegaOf (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) : SlimPi m →* SlimOmega m hemb :=
  of

/-- The original `F₃` inside the final slim tower. -/
noncomputable def slimOmegaEmb (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) : F₃ →* SlimOmega m hemb :=
  (slimOmegaOf m hemb).comp (slimPiF3Hom m)

/-- **The final tower really contains the stage-two copy of `F₃`.** -/
theorem slimOmegaEmb_injective (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) :
    Function.Injective (slimOmegaEmb m hemb) :=
  (HNNExtension.of_injective (slimShiftRangeEquiv m hemb)).comp hemb

/-- The orientation of `Omega.Tower.stable`: Mathlib's HNN relation is
`t x t⁻¹ = ρ(x)`, so the tower's stable element is `t⁻¹`. -/
noncomputable def slimOmegaStable (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) : SlimOmega m hemb :=
  (t : SlimOmega m hemb)⁻¹

/-- **The concrete third-stage relation.** -/
theorem slim_conj_stable (m : ℕ)
    (hemb : Function.Injective (slimPiF3Hom m)) (x : F₃) :
    (slimOmegaStable m hemb)⁻¹ * slimOmegaEmb m hemb x *
        slimOmegaStable m hemb =
      slimOmegaEmb m hemb ((⇑shiftAut)^[m] x) := by
  have h := HNNExtension.equiv_eq_conj (φ := slimShiftRangeEquiv m hemb)
    ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩
  rw [slimShiftRangeEquiv_apply] at h
  change (t : SlimOmega m hemb) * of (slimPiF3Hom m x) * t⁻¹ =
    of (slimPiF3Hom m ((⇑shiftAut)^[m] x))
  rw [← shiftEquiv_pow_apply]
  exact h.symm

end Omega
end Higman
end GroupApproximation
