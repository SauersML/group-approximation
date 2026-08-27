import GroupApproximation.Higman.OmegaFiniteLinkHNN
import GroupApproximation.Algebra.HNNFinitePresentation

/-!
# The finitely presented torsion-free Omega tower

The finite link stage contains the required rank-three copy.  Transporting
the block shift to that copy gives the final mapping-torus stage.  This file
packages the resulting concrete `Tower` and proves its `W` subgroup benign
from the selected cutter.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

theorem fatLinkPiF3Hom_rowElt (m : ℕ) (i : ℤ) :
    fatLinkPiF3Hom m (rowElt i) = fatLinkPiBaseEmb m (1, rowElt i) := by
  simp [rowElt, map_mul, map_zpow]

theorem fatLinkPiF3Hom_comp_rowHom (m : ℕ) :
    (fatLinkPiF3Hom m).comp rowHom =
      (fatLinkPiBaseEmb m).comp (MonoidHom.inr (FatCent3 m) F₃) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [fatLinkPiF3Hom_rowElt]

theorem fatLinkPiF3Hom_bElt (m : ℕ) (f : E) :
    fatLinkPiF3Hom m (bElt f) = fatPiRowCode m f := by
  change fatLinkPiF3Hom m (rowHom (elt f)) = _
  rw [← MonoidHom.comp_apply, fatLinkPiF3Hom_comp_rowHom]
  rfl

theorem fatLinkPiF3Hom_aElt (m : ℕ) (f : E) :
    fatLinkPiF3Hom m (aElt f) =
      (fatPiRowCode m f)⁻¹ * fatLinkPiF3Hom m a * fatPiRowCode m f := by
  rw [aElt, map_mul, map_mul, map_inv, fatLinkPiF3Hom_bElt]

/-- The block shift transported to the finite stage-two rank-three copy. -/
noncomputable def fatShiftRangeEquiv (m : ℕ) :
    (fatLinkPiF3Hom m).range ≃* (fatLinkPiF3Hom m).range :=
  ((MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).symm.trans
    ((shiftEquiv : MulAut F₃) ^ m)).trans
      (MonoidHom.ofInjective (fatLinkPiF3Hom_injective m))

theorem fatShiftRangeEquiv_apply (m : ℕ) (x : F₃) :
    ((fatShiftRangeEquiv m
        ⟨fatLinkPiF3Hom m x, ⟨x, rfl⟩⟩ : (fatLinkPiF3Hom m).range) :
        FatLinkPi m) =
      fatLinkPiF3Hom m (((shiftEquiv : MulAut F₃) ^ m) x) := by
  have hx : (MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).symm
      ⟨fatLinkPiF3Hom m x, ⟨x, rfl⟩⟩ = x := by
    apply (MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  change fatLinkPiF3Hom m (((shiftEquiv : MulAut F₃) ^ m)
      ((MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).symm
        ⟨fatLinkPiF3Hom m x, ⟨x, rfl⟩⟩)) = _
  rw [hx]

abbrev FatOmega (m : ℕ) : Type :=
  HNNExtension (FatLinkPi m) (fatLinkPiF3Hom m).range
    (fatLinkPiF3Hom m).range (fatShiftRangeEquiv m)

noncomputable def fatOmegaOf (m : ℕ) : FatLinkPi m →* FatOmega m := of

noncomputable def fatOmegaEmb (m : ℕ) : F₃ →* FatOmega m :=
  (fatOmegaOf m).comp (fatLinkPiF3Hom m)

theorem fatOmegaEmb_injective (m : ℕ) : Function.Injective (fatOmegaEmb m) :=
  (HNNExtension.of_injective (fatShiftRangeEquiv m)).comp
    (fatLinkPiF3Hom_injective m)

noncomputable def fatOmegaStable (m : ℕ) : FatOmega m := (t : FatOmega m)⁻¹

theorem fat_conj_stable (m : ℕ) (x : F₃) :
    (fatOmegaStable m)⁻¹ * fatOmegaEmb m x * fatOmegaStable m =
      fatOmegaEmb m ((⇑shiftAut)^[m] x) := by
  have h := HNNExtension.equiv_eq_conj (φ := fatShiftRangeEquiv m)
    ⟨fatLinkPiF3Hom m x, ⟨x, rfl⟩⟩
  rw [fatShiftRangeEquiv_apply] at h
  change (t : FatOmega m) * of (fatLinkPiF3Hom m x) * t⁻¹ =
    of (fatLinkPiF3Hom m ((⇑shiftAut)^[m] x))
  rw [← shiftEquiv_pow_apply]
  exact h.symm

noncomputable def fatOmegaGen (m : ℕ) (beta : E) : FatOmega m :=
  fatOmegaOf m (fatPiGen m beta)

theorem fat_conj_gen_top (m : ℕ) (beta : E) (hbeta : beta ∈ blockSet m) :
    (fatOmegaGen m beta)⁻¹ * fatOmegaEmb m a * fatOmegaGen m beta =
      fatOmegaEmb m (aElt beta) := by
  have h := congrArg (fatOmegaOf m) (fat_conj_gen m beta hbeta)
  rw [← fatLinkPiF3Hom_aElt] at h
  simpa only [fatOmegaGen, fatOmegaEmb, MonoidHom.comp_apply, map_mul, map_inv]
    using h

theorem fat_commute_gen_row_top
    {m : ℕ} (beta : E) (i : ℤ) :
    Commute (fatOmegaGen m beta) (fatOmegaEmb m (rowElt i)) := by
  have hprod : Commute
      (fatGenCode m beta, (1 : F₃)) ((1 : FatCent3 m), rowElt i) := by
    rw [Commute]
    ext <;> simp
  have hbase := Commute.map hprod (fatLinkPiBaseEmb m)
  have htop := Commute.map hbase (fatOmegaOf m)
  simpa only [fatOmegaGen, fatOmegaEmb, MonoidHom.comp_apply,
    fatPiGen, fatLinkPiF3Hom_rowElt] using htop

noncomputable def fatTower (m : ℕ) : Tower m where
  G := FatOmega m
  emb := fatOmegaEmb m
  emb_injective := fatOmegaEmb_injective m
  gen := fatOmegaGen m
  stable := fatOmegaStable m
  conj_stable := fat_conj_stable m
  conj_gen := fat_conj_gen_top m
  commute_row beta _ i _ := fat_commute_gen_row_top beta i

theorem isFinitelyPresented_fatOmega (m : ℕ) :
    Group.IsFinitelyPresented (FatOmega m) := by
  letI : Group.IsFinitelyPresented (FatLinkPi m) :=
    isFinitelyPresented_fatLinkPi m
  let e := MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)
  letI : Group.FG ↑((fatLinkPiF3Hom m).range) :=
    Group.fg_of_surjective e.toMonoidHom e.surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (fatShiftRangeEquiv m)

theorem isPowerTorsionFree_fatOmega (m : ℕ) :
    IsPowerTorsionFree (FatOmega m) :=
  HNNBritton.isPowerTorsionFree_hnn (fatShiftRangeEquiv m)
    (isPowerTorsionFree_fatLinkPi m)

noncomputable def fatFirstCoordinateEmb (m : ℕ) :
    FatCent3 m →* FatLinkPi m :=
  (fatLinkPiBaseEmb m).comp (MonoidHom.inl (FatCent3 m) F₃)

theorem fatFirstCoordinateEmb_injective (m : ℕ) :
    Function.Injective (fatFirstCoordinateEmb m) :=
  (fatLinkPiBaseEmb_injective m).comp MonoidHom.inl_injective

noncomputable def fatPiGenSub (m : ℕ) (B : Set E) : Subgroup (FatLinkPi m) :=
  Subgroup.closure (fatPiGen m '' (B ∩ blockSet m))

theorem fatPiGenSub_eq_map (m : ℕ) (B : Set E) :
    fatPiGenSub m B = (fatGenSub m B).map (fatFirstCoordinateEmb m) := by
  unfold fatPiGenSub fatGenSub fatPiGen fatGenCode fatFirstCoordinateEmb
  rw [MonoidHom.map_closure]
  rfl

theorem benignTF_fatPiGenSub {m : ℕ} {B : Set E}
    (hB : BenignTF (ASub B)) : BenignTF (fatPiGenSub m B) := by
  letI : Group.IsFinitelyPresented (FatLinkPi m) :=
    isFinitelyPresented_fatLinkPi m
  rw [fatPiGenSub_eq_map]
  exact BenignTF.mapEmb (isPowerTorsionFree_fatLinkPi m)
    (benignTF_fatGenSub hB) (fatFirstCoordinateEmb m)
    (fatFirstCoordinateEmb_injective m)

noncomputable def fatOmegaGenSub (m : ℕ) (B : Set E) :
    Subgroup (FatOmega m) :=
  Subgroup.closure (fatOmegaGen m '' (B ∩ blockSet m))

theorem fatOmegaGenSub_eq_map (m : ℕ) (B : Set E) :
    fatOmegaGenSub m B = (fatPiGenSub m B).map (fatOmegaOf m) := by
  unfold fatOmegaGenSub fatPiGenSub fatOmegaGen
  rw [MonoidHom.map_closure]
  rfl

theorem benignTF_fatOmegaGenSub {m : ℕ} {B : Set E}
    (hB : BenignTF (ASub B)) : BenignTF (fatOmegaGenSub m B) := by
  letI : Group.IsFinitelyPresented (FatOmega m) :=
    isFinitelyPresented_fatOmega m
  rw [fatOmegaGenSub_eq_map]
  exact BenignTF.mapEmb (isPowerTorsionFree_fatOmega m)
    (benignTF_fatPiGenSub hB) (fatOmegaOf m)
    (HNNExtension.of_injective (fatShiftRangeEquiv m))

/-- The complete finite tower has an unconditional torsion-free benign
`W` subgroup whenever the input code subgroup is torsion-free benign. -/
theorem benignTF_W_fatTower {m : ℕ} {B : Set E}
    (hB : BenignTF (ASub B)) : BenignTF (W (fatTower m) B) := by
  apply benignTF_W_of_gen (fatTower m)
    (isFinitelyPresented_fatOmega m) (isPowerTorsionFree_fatOmega m)
  simpa [fatOmegaGenSub, fatTower] using benignTF_fatOmegaGenSub hB

end Omega
end Higman
end GroupApproximation
