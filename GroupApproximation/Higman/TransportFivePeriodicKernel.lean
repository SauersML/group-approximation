import GroupApproximation.Higman.TransportFiveCoding
import GroupApproximation.Higman.RowKernel
import GroupApproximation.Higman.RowDeletionBenign
import GroupApproximation.Algebra.HNNFinitePresentation
import GroupApproximation.Algebra.HNNTorsionFree

/-!
# Higman's Section 5: the fixed periodic-row kernel

This module realizes the row image of the decoder kernel as the intersection
of two kernels in a finite cyclic-shift mapping torus, and proves that its
image in `F₃` is benign with a torsion-free witness.
-/

namespace GroupApproximation
namespace Higman
namespace Transport

open GroupApproximation.Higman.Conj

/-- Addition of one modulo `n+1`. -/
def cyclicSucc (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨((i : ℕ) + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- Subtraction of one modulo `n+1`. -/
def cyclicPred (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨((i : ℕ) + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

theorem cyclicPred_cyclicSucc (n : ℕ) (i : Fin (n + 1)) :
    cyclicPred n (cyclicSucc n i) = i := by
  apply Fin.ext
  simp only [cyclicPred, cyclicSucc, Fin.val_mk]
  rw [Nat.mod_add_mod]
  rw [show (i : ℕ) + 1 + n = (i : ℕ) + (n + 1) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem cyclicSucc_cyclicPred (n : ℕ) (i : Fin (n + 1)) :
    cyclicSucc n (cyclicPred n i) = i := by
  apply Fin.ext
  simp only [cyclicPred, cyclicSucc, Fin.val_mk]
  rw [Nat.mod_add_mod]
  rw [show (i : ℕ) + n + 1 = (i : ℕ) + (n + 1) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem cyclicSucc_letterOf (n : ℕ) (p : ℤ) :
    cyclicSucc n (letterOf n p) = letterOf n (p + 1) := by
  apply Fin.ext
  simp only [cyclicSucc, letterOf, Fin.val_mk]
  have hm : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hnonneg : (0 : ℤ) ≤ p % ((n : ℤ) + 1) :=
    Int.emod_nonneg p (ne_of_gt hm)
  have htoNat :
      (((p % ((n : ℤ) + 1)) + 1) % ((n : ℤ) + 1)).toNat =
        ((p % ((n : ℤ) + 1)).toNat + 1) % (n + 1) := by
    rw [Int.toNat_emod (by omega) hm.le]
    have hmodulus : (((n : ℤ) + 1).toNat) = n + 1 := by omega
    rw [hmodulus]
    have hadd : ((p % ((n : ℤ) + 1)) + 1).toNat =
        (p % ((n : ℤ) + 1)).toNat + 1 := by omega
    rw [hadd]
  rw [← htoNat, Int.emod_add_emod]

theorem cyclicPred_letterOf (n : ℕ) (p : ℤ) :
    cyclicPred n (letterOf n p) = letterOf n (p - 1) := by
  apply Fin.ext
  simp only [cyclicPred, letterOf, Fin.val_mk]
  have hm : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hnonneg : (0 : ℤ) ≤ p % ((n : ℤ) + 1) :=
    Int.emod_nonneg p (ne_of_gt hm)
  have htoNat :
      (((p % ((n : ℤ) + 1)) + (n : ℤ)) % ((n : ℤ) + 1)).toNat =
        ((p % ((n : ℤ) + 1)).toNat + n) % (n + 1) := by
    rw [Int.toNat_emod (by omega) hm.le]
    simp only [Int.toNat_add_nat hnonneg, Int.toNat_natCast_add_one]
  have hmod :
      ((p % ((n : ℤ) + 1)) + (n : ℤ)) % ((n : ℤ) + 1) =
        (p - 1) % ((n : ℤ) + 1) := by
    rw [Int.emod_add_emod]
    rw [show p + (n : ℤ) = (p - 1) + ((n : ℤ) + 1) by omega,
      Int.add_emod_right]
  rw [← htoNat, hmod]

/-- The cyclic predecessor on the finite-rank free group. -/
def cyclicPredHom (n : ℕ) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.map (cyclicPred n)

/-- The inverse cyclic successor on the finite-rank free group. -/
def cyclicSuccHom (n : ℕ) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.map (cyclicSucc n)

theorem cyclicPredHom_comp_cyclicSuccHom (n : ℕ) :
    (cyclicPredHom n).comp (cyclicSuccHom n) =
      MonoidHom.id (FreeGroup (Fin (n + 1))) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [cyclicPredHom, cyclicSuccHom, cyclicPred_cyclicSucc]

theorem cyclicSuccHom_comp_cyclicPredHom (n : ℕ) :
    (cyclicSuccHom n).comp (cyclicPredHom n) =
      MonoidHom.id (FreeGroup (Fin (n + 1))) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [cyclicPredHom, cyclicSuccHom, cyclicSucc_cyclicPred]

/-- The cyclic predecessor as a free-group automorphism. -/
def cyclicFreeEquiv (n : ℕ) :
    FreeGroup (Fin (n + 1)) ≃* FreeGroup (Fin (n + 1)) where
  toFun := cyclicPredHom n
  invFun := cyclicSuccHom n
  left_inv x := congrArg (fun f : FreeGroup (Fin (n + 1)) →*
      FreeGroup (Fin (n + 1)) => f x) (cyclicSuccHom_comp_cyclicPredHom n)
  right_inv x := congrArg (fun f : FreeGroup (Fin (n + 1)) →*
      FreeGroup (Fin (n + 1)) => f x) (cyclicPredHom_comp_cyclicSuccHom n)
  map_mul' := map_mul _

@[simp] theorem cyclicFreeEquiv_of (n : ℕ) (i : Fin (n + 1)) :
    cyclicFreeEquiv n (FreeGroup.of i) = FreeGroup.of (cyclicPred n i) := by
  simp [cyclicFreeEquiv, cyclicPredHom]

@[simp] theorem cyclicFreeEquiv_symm_of (n : ℕ) (i : Fin (n + 1)) :
    (cyclicFreeEquiv n).symm (FreeGroup.of i) = FreeGroup.of (cyclicSucc n i) := by
  simp [cyclicFreeEquiv, cyclicSuccHom]

/-- The cyclic automorphism transported to the top subgroup. -/
def cyclicTop (n : ℕ) :
    ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1)))) ≃*
      ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1)))) :=
  Subgroup.topEquiv.trans ((cyclicFreeEquiv n).trans Subgroup.topEquiv.symm)

@[simp] theorem coe_cyclicTop (n : ℕ)
    (x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
    ((cyclicTop n x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
      FreeGroup (Fin (n + 1))) = cyclicFreeEquiv n (x : FreeGroup (Fin (n + 1))) := rfl

@[simp] theorem coe_cyclicTop_symm (n : ℕ)
    (x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
    (((cyclicTop n).symm x : ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1))))) :
      FreeGroup (Fin (n + 1))) =
        (cyclicFreeEquiv n).symm (x : FreeGroup (Fin (n + 1))) := rfl

/-- The finite cyclic-shift mapping torus. -/
abbrev CyclicMappingTorus (n : ℕ) : Type :=
  HNNExtension (FreeGroup (Fin (n + 1))) ⊤ ⊤ (cyclicTop n)

theorem cyclicMappingTorus_fp (n : ℕ) :
    Group.IsFinitelyPresented (CyclicMappingTorus n) := by
  letI : Group.FG ↥(⊤ : Subgroup (FreeGroup (Fin (n + 1)))) :=
    Group.fg_of_surjective
      (f := (Subgroup.topEquiv (G := FreeGroup (Fin (n + 1)))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := FreeGroup (Fin (n + 1)))).symm.surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension (cyclicTop n)

theorem cyclicMappingTorus_torsionFree (n : ℕ) :
    IsPowerTorsionFree (CyclicMappingTorus n) :=
  HNNBritton.isPowerTorsionFree_hnn (cyclicTop n)
    IsPowerTorsionFree.of_isMulTorsionFree

/-- The rank-two detector: `b` enters the zero-th cyclic coordinate and `c`
is the stable letter. -/
def periodicHom (n : ℕ) : Row.F₀ →* CyclicMappingTorus n :=
  FreeGroup.lift fun i : Fin 2 =>
    if i = 0 then HNNExtension.of (FreeGroup.of (0 : Fin (n + 1)))
    else HNNExtension.t

@[simp] theorem periodicHom_b (n : ℕ) :
    periodicHom n Row.b = HNNExtension.of (FreeGroup.of (0 : Fin (n + 1))) := by
  simp [periodicHom, Row.b]

@[simp] theorem periodicHom_c (n : ℕ) :
    periodicHom n Row.c = HNNExtension.t := by
  simp [periodicHom, Row.c]

theorem cyclic_conj (n : ℕ) (x : FreeGroup (Fin (n + 1))) :
    (HNNExtension.t : CyclicMappingTorus n) * HNNExtension.of x *
        (HNNExtension.t : CyclicMappingTorus n)⁻¹ =
      HNNExtension.of (cyclicFreeEquiv n x) := by
  have h := HNNExtension.equiv_eq_conj (φ := cyclicTop n)
    ⟨x, Subgroup.mem_top x⟩
  rw [coe_cyclicTop] at h
  exact h.symm

theorem cyclic_conj_symm (n : ℕ) (x : FreeGroup (Fin (n + 1))) :
    (HNNExtension.t : CyclicMappingTorus n)⁻¹ * HNNExtension.of x *
        (HNNExtension.t : CyclicMappingTorus n) =
      HNNExtension.of ((cyclicFreeEquiv n).symm x) := by
  have h := HNNExtension.equiv_symm_eq_conj (φ := cyclicTop n)
    ⟨x, Subgroup.mem_top x⟩
  simpa only [coe_cyclicTop_symm] using h.symm

theorem row_succ (i : ℤ) : Row.row (i + 1) = Row.c⁻¹ * Row.row i * Row.c := by
  unfold Row.row
  simp only [zpow_neg, zpow_add, zpow_one]
  group

theorem row_pred (i : ℤ) : Row.row (i - 1) = Row.c * Row.row i * Row.c⁻¹ := by
  unfold Row.row
  simp only [zpow_neg, zpow_sub, zpow_one]
  group

/-- The periodic detector sends the `i`-th row basis element to the decoded
residue class of `i`. -/
theorem periodicHom_row (n : ℕ) (i : ℤ) :
    periodicHom n (Row.row i) = HNNExtension.of (FreeGroup.of (letterOf n i)) := by
  induction i using Int.induction_on with
  | zero =>
      rw [Row.row_zero, periodicHom_b]
      congr 2
  | succ i ih =>
      rw [row_succ, map_mul, map_mul, map_inv, periodicHom_c, ih,
        cyclic_conj_symm, cyclicFreeEquiv_symm_of, cyclicSucc_letterOf]
  | pred i ih =>
      rw [row_pred, map_mul, map_mul, map_inv, periodicHom_c, ih,
        cyclic_conj, cyclicFreeEquiv_of, cyclicPred_letterOf]

/-- The detector square commutes on the whole countable row free group. -/
theorem periodicHom_comp_basisHom (n : ℕ) :
    (periodicHom n).comp Row.basisHom =
      (HNNExtension.of : FreeGroup (Fin (n + 1)) →* CyclicMappingTorus n).comp
        (decodeHom n) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Row.basisHom_of, decodeHom_of,
    periodicHom_row]

/-- In the rank-two row carrier, the decoder kernel is the intersection of
the row kernel and the cyclic detector kernel. -/
theorem map_basisHom_ker_decodeHom (n : ℕ) :
    (MonoidHom.ker (decodeHom n)).map Row.basisHom =
      MonoidHom.ker Row.expHom ⊓ MonoidHom.ker (periodicHom n) := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Row.Row_eq_ker, ← Row.range_basisHom]
      exact ⟨w, rfl⟩
    · apply MonoidHom.mem_ker.mpr
      have hcomp := congrArg (fun f : FreeGroup ℤ →* CyclicMappingTorus n => f w)
        (periodicHom_comp_basisHom n)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hw,
        map_one] at hcomp
      exact hcomp
  · intro x hx
    rw [← Row.Row_eq_ker, ← Row.range_basisHom] at hx
    obtain ⟨w, hw⟩ := hx.1
    subst x
    refine Subgroup.mem_map.mpr ⟨w, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have hcomp := congrArg (fun f : FreeGroup ℤ →* CyclicMappingTorus n => f w)
      (periodicHom_comp_basisHom n)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hcomp
    have hp : periodicHom n (Row.basisHom w) = 1 := MonoidHom.mem_ker.mp hx.2
    rw [hp] at hcomp
    exact HNNExtension.of_injective (φ := cyclicTop n) (by simpa using hcomp.symm)

/-- **The periodic row kernel is benign with a torsion-free witness.** -/
theorem benignTF_periodicRowKernel (n : ℕ) : BenignTF (periodicRowKernel n) := by
  letI : Group.IsFinitelyPresented (CyclicMappingTorus n) := cyclicMappingTorus_fp n
  have hexp : BenignTF (MonoidHom.ker Row.expHom) :=
    ⟨TorsionFreeBenignWitness.ker IsPowerTorsionFree.of_isMulTorsionFree
      IsPowerTorsionFree.of_isMulTorsionFree Row.expHom⟩
  have hper : BenignTF (MonoidHom.ker (periodicHom n)) :=
    ⟨TorsionFreeBenignWitness.ker IsPowerTorsionFree.of_isMulTorsionFree
      (cyclicMappingTorus_torsionFree n) (periodicHom n)⟩
  have hint : BenignTF ((MonoidHom.ker (decodeHom n)).map Row.basisHom) := by
    rw [map_basisHom_ker_decodeHom]
    exact BenignTF.inf hexp hper
  have hmap := BenignTF.mapEmb IsPowerTorsionFree.of_isMulTorsionFree hint
    inclHom inclHom_injective
  rw [Subgroup.map_map, inclHom_comp_basisHom] at hmap
  exact hmap

end Transport
end Higman
end GroupApproximation
