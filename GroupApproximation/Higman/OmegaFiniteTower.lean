import GroupApproximation.Higman.OmegaFiniteLinkHNN
import GroupApproximation.Higman.OmegaTowerStageThree

/-!
# The finite asymmetric Omega tower

This file adds the final shift HNN stage to `FatLinkPi`.  Unlike the refuted
modified tower, its stage-two link is the exact benign graph of the ordered
pairs `(g_beta,b_beta^-1)`.  The result is an unconditional finitely presented
torsion-free `Omega.Tower`, and its selected generating subgroup is benign.
It is a structural checkpoint, not an Omega closure: the direct-product base
makes every selected code commute with every row.  The valid half-line repair
must instead keep those elements in the same noncommuting semantic factor.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

theorem fatLinkPiF3Hom_rowElt (m : ℕ) (i : ℤ) :
    fatLinkPiF3Hom m (rowElt i) = fatLinkPiBaseEmb m (1, rowElt i) := by
  unfold rowElt
  rw [map_mul, map_mul, map_zpow, map_zpow,
    fatLinkPiF3Hom_b, fatLinkPiF3Hom_c]
  rw [← map_zpow, ← map_zpow, ← map_mul, ← map_mul]
  apply congrArg (fatLinkPiBaseEmb m)
  apply Prod.ext <;> simp

theorem fatLinkPiF3Hom_comp_rowHom (m : ℕ) :
    (fatLinkPiF3Hom m).comp rowHom =
      ((fatLinkPiBaseEmb m).comp
        (MonoidHom.inr (FatCent3 m) F₃)).comp rowHom := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, rowHom_of]
  change fatLinkPiF3Hom m (rowElt i) = fatLinkPiBaseEmb m (1, rowElt i)
  exact fatLinkPiF3Hom_rowElt m i

theorem fatLinkPiF3Hom_bElt (m : ℕ) (f : E) :
    fatLinkPiF3Hom m (bElt f) = fatPiRowCode m f := by
  unfold bElt fatPiRowCode
  exact DFunLike.congr_fun (fatLinkPiF3Hom_comp_rowHom m) (elt f)

theorem fatLinkPiF3Hom_aElt (m : ℕ) (f : E) :
    fatLinkPiF3Hom m (aElt f) =
      (fatPiRowCode m f)⁻¹ * fatLinkPiF3Hom m a * fatPiRowCode m f := by
  unfold aElt
  rw [map_mul, map_mul, map_inv, fatLinkPiF3Hom_bElt]

/-- Transport the `m`-shift to the finite stage-two semantic copy. -/
noncomputable def fatShiftRangeEquiv (m : ℕ) :
    (fatLinkPiF3Hom m).range ≃* (fatLinkPiF3Hom m).range :=
  ((MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).symm.trans
    ((shiftEquiv : MulAut F₃) ^ m)).trans
      (MonoidHom.ofInjective (fatLinkPiF3Hom_injective m))

theorem fatShiftRangeEquiv_apply (m : ℕ) (x : F₃) :
    ((fatShiftRangeEquiv m
        ⟨fatLinkPiF3Hom m x, ⟨x, rfl⟩⟩ :
          (fatLinkPiF3Hom m).range) : FatLinkPi m) =
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

/-- The final finite asymmetric shift stage. -/
noncomputable abbrev FatOmega (m : ℕ) : Type :=
  HNNExtension (FatLinkPi m) (fatLinkPiF3Hom m).range
    (fatLinkPiF3Hom m).range (fatShiftRangeEquiv m)

noncomputable def fatOmegaOf (m : ℕ) : FatLinkPi m →* FatOmega m :=
  HNNExtension.of

noncomputable def fatOmegaEmb (m : ℕ) : F₃ →* FatOmega m :=
  (fatOmegaOf m).comp (fatLinkPiF3Hom m)

theorem fatOmegaEmb_injective (m : ℕ) : Function.Injective (fatOmegaEmb m) :=
  (HNNExtension.of_injective (fatShiftRangeEquiv m)).comp
    (fatLinkPiF3Hom_injective m)

noncomputable def fatOmegaStable (m : ℕ) : FatOmega m :=
  (t : FatOmega m)⁻¹

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

/-- **Scope obstruction.**  The direct-product finite link makes a selected
code commute with every row, not merely with the right tail. -/
theorem fatOmegaGen_commute_all_rows (m : ℕ) (beta : E) (i : ℤ) :
    Commute (fatOmegaGen m beta) (fatOmegaEmb m (rowElt i)) := by
  have hbase : Commute
      ((fatGenCode m beta, 1) : FatCent3 m × F₃) (1, rowElt i) := by
    apply Prod.ext <;> simp
  have htop := (hbase.map (fatLinkPiBaseEmb m)).map (fatOmegaOf m)
  simpa only [fatOmegaGen, fatPiGen, fatOmegaEmb, MonoidHom.comp_apply,
    fatLinkPiF3Hom_rowElt] using htop

/-- The finite structural tower.  Its stronger all-row commutation prevents
using it for the one-sided descent. -/
noncomputable def fatTower (m : ℕ) : Tower m where
  G := FatOmega m
  emb := fatOmegaEmb m
  emb_injective := fatOmegaEmb_injective m
  gen := fatOmegaGen m
  stable := fatOmegaStable m
  conj_stable := fat_conj_stable m
  conj_gen beta hbeta := by
    have h := congrArg (fatOmegaOf m) (fat_conj_gen m beta hbeta)
    have hrow := fatLinkPiF3Hom_aElt m beta
    simpa only [fatOmegaGen, fatOmegaEmb, MonoidHom.comp_apply, map_mul,
      map_inv, hrow] using h
  commute_row beta _ i _ := by
    exact fatOmegaGen_commute_all_rows m beta i

theorem isFinitelyPresented_fatOmega (m : ℕ) :
    Group.IsFinitelyPresented (FatOmega m) := by
  letI : Group.IsFinitelyPresented (FatLinkPi m) :=
    isFinitelyPresented_fatLinkPi m
  letI : Group.FG F₃ := inferInstance
  letI : Group.FG ↑((fatLinkPiF3Hom m).range) :=
    Group.fg_of_surjective
      (f := (MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).toMonoidHom)
      (MonoidHom.ofInjective (fatLinkPiF3Hom_injective m)).surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (fatShiftRangeEquiv m)

theorem isPowerTorsionFree_fatOmega (m : ℕ) :
    IsPowerTorsionFree (FatOmega m) :=
  HNNBritton.isPowerTorsionFree_hnn
    (fatShiftRangeEquiv m) (isPowerTorsionFree_fatLinkPi m)

/-- The selected first-coordinate subgroup mapped through both finite HNN
stages. -/
noncomputable def fatGenToOmega (m : ℕ) : FatCent3 m →* FatOmega m :=
  (fatOmegaOf m).comp
    ((fatLinkPiBaseEmb m).comp (MonoidHom.inl (FatCent3 m) F₃))

theorem fatGenToOmega_injective (m : ℕ) : Function.Injective (fatGenToOmega m) :=
  (HNNExtension.of_injective (fatShiftRangeEquiv m)).comp
    ((fatLinkPiBaseEmb_injective m).comp (fun _ _ h => congrArg Prod.fst h))

theorem fatTower_genSub_eq_map (m : ℕ) (B : Set E) :
    Subgroup.closure ((fatTower m).gen '' (B ∩ blockSet m)) =
      (fatGenSub m B).map (fatGenToOmega m) := by
  unfold fatGenSub fatTower fatOmegaGen fatPiGen fatGenToOmega
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨beta, hbeta, rfl⟩
    exact ⟨fatGenCode m beta, ⟨beta, hbeta, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨beta, hbeta, rfl⟩, rfl⟩
    exact ⟨beta, hbeta, rfl⟩

theorem benignTF_fatTower_genSub {m : ℕ} {B : Set E}
    (hB : BenignTF (ASub B)) :
    BenignTF (Subgroup.closure ((fatTower m).gen '' (B ∩ blockSet m))) := by
  rw [fatTower_genSub_eq_map]
  letI : Group.IsFinitelyPresented (FatCent3 m) :=
    isFinitelyPresented_fatCent3 m
  letI : Group.FG (FatCent3 m) :=
    ProductFinitePresentation.fg_of_isFinitelyPresented (FatCent3 m)
  letI : Group.IsFinitelyPresented (FatOmega m) :=
    isFinitelyPresented_fatOmega m
  exact BenignTF.mapEmb (isPowerTorsionFree_fatOmega m)
    (benignTF_fatGenSub hB) (fatGenToOmega m) (fatGenToOmega_injective m)

/-- The `W` subgroup is benign, but the all-row obstruction above means this
does not provide the descent field of `TowerClosure`. -/
theorem benignTF_W_fatTower {m : ℕ} {B : Set E}
    (hB : BenignTF (ASub B)) : BenignTF (W (fatTower m) B) := by
  exact benignTF_W_of_gen (fatTower m)
    (isFinitelyPresented_fatOmega m) (isPowerTorsionFree_fatOmega m)
    (benignTF_fatTower_genSub hB)

end Omega
end Higman
end GroupApproximation
