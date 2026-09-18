import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPPres
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPLevel
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Root subgroups `ℤ[1/m] → P m` (bh-met-91m)

Write `R = ℤ[1/m]` and `x = m ∈ R`.  Since `χ_α(α) = 2`, the pair `T α, Y α` of `P m` satisfies
`T α Y α T α⁻¹ = Y α ^ (m ^ 2)`, so `ElemFPCharZeroStFourFPLevel` (with `q = x ^ 2`) gives a map
`czStFourFP_XP m α : R → P m`, additive, extending `n ↦ Y α ^ n`.  Conjugation by `T s` scales
it by `x ^ χ_s(α)` when `χ_s(α) ≥ 0` (`czStFourFP_XP_conj_T`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- The ring `ℤ[1/m]`. -/
abbrev czStFourFP_R (m : ℕ) : Type := Localization.Away (m : ℤ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_R

/-- Every element of `ℤ[1/m]` becomes integral after multiplying by a power of `m ^ 2`. -/
theorem czStFourFP_surj (m : ℕ) (r : czStFourFP_R m) :
    ∃ k : ℕ, ∃ n : ℤ, (((m : ℤ) : czStFourFP_R m) ^ 2) ^ k * r = (n : czStFourFP_R m) := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (m : ℤ) r
  rw [eq_intCast, eq_intCast] at h
  refine ⟨k, (m : ℤ) ^ k * a, ?_⟩
  rw [Int.cast_mul, Int.cast_pow, ← h]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_surj

/-- `ℤ → ℤ[1/m]` is injective for `m > 0`. -/
theorem czStFourFP_intCast_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (Int.cast : ℤ → czStFourFP_R m) := by
  intro a b h
  apply IsLocalization.injective (czStFourFP_R m)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (show (m : ℤ) ≠ 0 by omega))
  exact (eq_intCast (algebraMap ℤ (czStFourFP_R m)) a).trans
    (h.trans (eq_intCast (algebraMap ℤ (czStFourFP_R m)) b).symm)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_intCast_injective

theorem czStFourFP_hq (m : ℕ) :
    ((m : ℤ) : czStFourFP_R m) ^ 2 = (((m : ℤ) ^ 2 : ℤ) : czStFourFP_R m) :=
  (Int.cast_pow _ _).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_hq

/-- The unit `m` of `ℤ[1/m]`. -/
noncomputable def czStFourFP_u (m : ℕ) : (czStFourFP_R m)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := czStFourFP_R m) (m : ℤ)).unit

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_u

theorem czStFourFP_u_val (m : ℕ) :
    ((czStFourFP_u m : (czStFourFP_R m)ˣ) : czStFourFP_R m) = ((m : ℤ) : czStFourFP_R m) := by
  rw [czStFourFP_u, IsUnit.unit_spec, eq_intCast]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_u_val

theorem czStFourFP_u_zpow (m : ℕ) {e : ℤ} (h : 0 ≤ e) :
    ((czStFourFP_u m ^ e : (czStFourFP_R m)ˣ) : czStFourFP_R m) =
      (((m : ℤ) ^ e.toNat : ℤ) : czStFourFP_R m) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [zpow_natCast, Units.val_pow_eq_pow_val, czStFourFP_u_val, Int.toNat_natCast,
    Int.cast_pow]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_u_zpow

/-- The Baumslag–Solitar relation `T α Y α T α⁻¹ = Y α ^ (m ^ 2)`. -/
theorem czStFourFP_ht (m : ℕ) (α : czStFourFP_Root) :
    czStFourFP_T m α * czStFourFP_Y m α * (czStFourFP_T m α)⁻¹ =
      czStFourFP_Y m α ^ ((m : ℤ) ^ 2) := by
  have h := czStFourFP_T_conj_Y m α α (by rw [czStFourFP_chi_ab α.2]; norm_num)
  rw [czStFourFP_chi_ab α.2] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_ht

/-- The root subgroup `ℤ[1/m] → P m` in the direction `α`. -/
noncomputable def czStFourFP_XP (m : ℕ) (α : czStFourFP_Root) (r : czStFourFP_R m) :
    czStFourFP_P m :=
  czStFourFP_X (czStFourFP_T m α) (czStFourFP_Y m α) (czStFourFP_surj m) r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP

theorem czStFourFP_XP_int (m : ℕ) (hm : 0 < m) (α : czStFourFP_Root) (n : ℤ) :
    czStFourFP_XP m α (n : czStFourFP_R m) = czStFourFP_Y m α ^ n :=
  czStFourFP_X_int (czStFourFP_ht m α) (czStFourFP_hq m) (czStFourFP_intCast_injective m hm)
    (czStFourFP_surj m) n

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP_int

theorem czStFourFP_XP_add (m : ℕ) (hm : 0 < m) (α : czStFourFP_Root) (r s : czStFourFP_R m) :
    czStFourFP_XP m α (r + s) = czStFourFP_XP m α r * czStFourFP_XP m α s :=
  czStFourFP_X_add (czStFourFP_ht m α) (czStFourFP_hq m) (czStFourFP_intCast_injective m hm)
    (czStFourFP_surj m) r s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP_add

theorem czStFourFP_XP_rep (m : ℕ) (hm : 0 < m) (α : czStFourFP_Root) (r : czStFourFP_R m)
    (k : ℕ) (n : ℤ) (h : (((m : ℤ) : czStFourFP_R m) ^ 2) ^ k * r = (n : czStFourFP_R m)) :
    czStFourFP_XP m α r = (czStFourFP_T m α ^ k)⁻¹ * czStFourFP_Y m α ^ n * czStFourFP_T m α ^ k :=
  czStFourFP_X_rep (czStFourFP_ht m α) (czStFourFP_hq m) (czStFourFP_intCast_injective m hm)
    (czStFourFP_surj m) r k n h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP_rep

theorem czStFourFP_XP_conj_t (m : ℕ) (hm : 0 < m) (α : czStFourFP_Root) (r : czStFourFP_R m) :
    czStFourFP_T m α * czStFourFP_XP m α r * (czStFourFP_T m α)⁻¹ =
      czStFourFP_XP m α (((m : ℤ) : czStFourFP_R m) ^ 2 * r) :=
  czStFourFP_X_conj_t (czStFourFP_ht m α) (czStFourFP_hq m)
    (czStFourFP_intCast_injective m hm) (czStFourFP_surj m) r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP_conj_t

/-- **Scaling.**  For `χ = χ_s(α) ≥ 0`, `T s XP_α(r) T s⁻¹ = XP_α(m ^ χ r)`. -/
theorem czStFourFP_XP_conj_T (m : ℕ) (hm : 0 < m) (s α : czStFourFP_Root)
    (h : 0 ≤ czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2) (r : czStFourFP_R m) :
    czStFourFP_T m s * czStFourFP_XP m α r * (czStFourFP_T m s)⁻¹ =
      czStFourFP_XP m α (((m : ℤ) : czStFourFP_R m) ^
        (czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2).toNat * r) := by
  refine czStFourFP_X_conj_of (czStFourFP_ht m α) (czStFourFP_hq m)
    (czStFourFP_intCast_injective m hm) (czStFourFP_surj m)
    (ρ := ((m : ℤ) : czStFourFP_R m) ^ (czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2).toNat) ?_
    (czStFourFP_T_conj_swap m s α) r
  have e := czStFourFP_X_int (czStFourFP_ht m α) (czStFourFP_hq m)
    (czStFourFP_intCast_injective m hm) (czStFourFP_surj m)
    ((m : ℤ) ^ (czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2).toNat)
  rw [Int.cast_pow] at e
  rw [czStFourFP_T_conj_Y m s α h]
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP_conj_T

/-- The case `χ_s(α) = 1`. -/
theorem czStFourFP_XP_conj_T_one (m : ℕ) (hm : 0 < m) (s α : czStFourFP_Root)
    (he : czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2 = 1) (r : czStFourFP_R m) :
    czStFourFP_T m s * czStFourFP_XP m α r * (czStFourFP_T m s)⁻¹ =
      czStFourFP_XP m α (((m : ℤ) : czStFourFP_R m) * r) := by
  have h := czStFourFP_XP_conj_T m hm s α (by rw [he]; norm_num) r
  rw [he, show (1 : ℤ).toNat = 1 from rfl, pow_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_XP_conj_T_one

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
