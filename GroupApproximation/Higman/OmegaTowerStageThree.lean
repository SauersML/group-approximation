import GroupApproximation.Higman.OmegaTowerStageTwoBritton

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
noncomputable def slimShiftRangeEquiv (m : ℕ) :
    (slimPiF3Hom m).range ≃* (slimPiF3Hom m).range :=
  ((MonoidHom.ofInjective (slimPiF3Hom_injective m)).symm.trans
    ((shiftEquiv : MulAut F₃) ^ m)).trans
      (MonoidHom.ofInjective (slimPiF3Hom_injective m))

theorem shiftEquiv_pow_apply (m : ℕ) (x : F₃) :
    ((shiftEquiv : MulAut F₃) ^ m) x = (⇑shiftAut)^[m] x := by
  induction m generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]
      rfl

theorem slimShiftRangeEquiv_apply (m : ℕ) (x : F₃) :
    ((slimShiftRangeEquiv m
        ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩ : (slimPiF3Hom m).range) : SlimPi m) =
      slimPiF3Hom m (((shiftEquiv : MulAut F₃) ^ m) x) := by
  have hx : (MonoidHom.ofInjective (slimPiF3Hom_injective m)).symm
      ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩ = x := by
    apply (MonoidHom.ofInjective (slimPiF3Hom_injective m)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  change slimPiF3Hom m (((shiftEquiv : MulAut F₃) ^ m)
      ((MonoidHom.ofInjective (slimPiF3Hom_injective m)).symm
        ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩)) = _
  rw [hx]

/-- The slim third stage, an HNN extension of stage two along the transported
`m`-fold shift. -/
abbrev SlimOmega (m : ℕ) : Type :=
  HNNExtension (SlimPi m) (slimPiF3Hom m).range (slimPiF3Hom m).range
    (slimShiftRangeEquiv m)

/-- The stage-two base inside the final slim tower. -/
noncomputable def slimOmegaOf (m : ℕ) : SlimPi m →* SlimOmega m :=
  of

/-- The original `F₃` inside the final slim tower. -/
noncomputable def slimOmegaEmb (m : ℕ) : F₃ →* SlimOmega m :=
  (slimOmegaOf m).comp (slimPiF3Hom m)

/-- **The final tower really contains the stage-two copy of `F₃`.** -/
theorem slimOmegaEmb_injective (m : ℕ) : Function.Injective (slimOmegaEmb m) :=
  (HNNExtension.of_injective (slimShiftRangeEquiv m)).comp
    (slimPiF3Hom_injective m)

/-- The orientation of `Omega.Tower.stable`: Mathlib's HNN relation is
`t x t⁻¹ = ρ(x)`, so the tower's stable element is `t⁻¹`. -/
noncomputable def slimOmegaStable (m : ℕ) : SlimOmega m :=
  (t : SlimOmega m)⁻¹

/-- **The concrete third-stage relation.** -/
theorem slim_conj_stable (m : ℕ) (x : F₃) :
    (slimOmegaStable m)⁻¹ * slimOmegaEmb m x * slimOmegaStable m =
      slimOmegaEmb m ((⇑shiftAut)^[m] x) := by
  have h := HNNExtension.equiv_eq_conj (φ := slimShiftRangeEquiv m)
    ⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩
  rw [slimShiftRangeEquiv_apply] at h
  change (t : SlimOmega m) * of (slimPiF3Hom m x) * t⁻¹ =
    of (slimPiF3Hom m ((⇑shiftAut)^[m] x))
  rw [← shiftEquiv_pow_apply]
  exact h.symm

/-! ## The completed three-stage tower interface -/

/-- The second-copy code at the top of the slim tower. -/
noncomputable def slimOmegaGen (m : ℕ) (β : E) : SlimOmega m :=
  slimOmegaOf m (slimPiOf m (slimGenCode m β))

/-- **The three concrete HNN stages form an unconditional `Omega.Tower`.**
The remaining `OmegaTowerInput` work is now entirely in `TowerClosure`: the
fat-tower benignness transfer and the slim-tower normal-form descent. -/
noncomputable def slimTower (m : ℕ) : Tower m where
  G := SlimOmega m
  emb := slimOmegaEmb m
  emb_injective := slimOmegaEmb_injective m
  gen := slimOmegaGen m
  stable := slimOmegaStable m
  conj_stable := slim_conj_stable m
  conj_gen β hβ := by
    have h := congrArg (slimOmegaOf m) (slim_conj_gen m β hβ)
    simpa only [slimOmegaGen, slimOmegaEmb, MonoidHom.comp_apply, map_mul,
      map_inv, slimPiF3Hom_a] using h
  commute_row β hβ i hi := by
    have hcomm := commute_genHom_row_slim (y := aElt β) hi
    have hpi : Commute
        (slimPiOf m (slimGenCode m β))
        (slimPiOf m (emb3 (rowOut m) (Row.row i))) := by
      exact Commute.map hcomm (slimPiOf m)
    have htop := Commute.map hpi (slimOmegaOf m)
    simpa only [slimOmegaGen, slimOmegaEmb, MonoidHom.comp_apply,
      slimGenCode, slimPiF3Hom_rowElt, slimPiRowEmb] using htop

end Omega
end Higman
end GroupApproximation
