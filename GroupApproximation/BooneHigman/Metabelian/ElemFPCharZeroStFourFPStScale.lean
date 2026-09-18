import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStChar
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPGroup
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# `H_ab(v)` scales every root subgroup by its character (bh-met-91m)

* `czStFourFP_H_conj`: `H_ab(v) x_ij(r) H_ab(v)⁻¹ = x_ij(v ^ χ_ab(i,j) · r)`, for any index
  type with a third index next to any two (e.g. `Fin 4`).
* `czStFourFP_H_zpow_conj`: the same for powers of `H_ab(v)`.
* `czStFourFP_H_central`: the commutator-type element `(H' H)⁻¹ (H H')` is central, since
  conjugation by `H H'` and by `H' H` agree on every generator.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

section Cases

theorem czStFourFP_Hc_ab {a b k : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x a b hab r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x a b hab (((v ^ czStFourFP_chi a b a b : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_ab hab, zpow_two, Units.val_mul,
    czStFourFP_H_ab a b k hab hka.symm hkb.symm]
  congr 1
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_ab

theorem czStFourFP_Hc_ba {a b k : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (hba : b ≠ a) (v : Rˣ) (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x b a hba r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x b a hba (((v ^ czStFourFP_chi a b b a : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_ba hab, zpow_neg, zpow_two, mul_inv_rev, Units.val_mul,
    czStFourFP_H_ba a b k hab hka.symm hkb.symm]
  congr 1
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_ba

theorem czStFourFP_Hc_ak {a b k : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (hak : a ≠ k) (v : Rˣ) (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x a k hak r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x a k hak (((v ^ czStFourFP_chi a b a k : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_ak hab hka hkb, zpow_one, czStFourFP_H_ak a b k hab hak hkb.symm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_ak

theorem czStFourFP_Hc_bk {a b k : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (hbk : b ≠ k) (v : Rˣ) (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x b k hbk r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x b k hbk (((v ^ czStFourFP_chi a b b k : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_bk hab hka hkb, zpow_neg_one, czStFourFP_H_bk a b k hab hka.symm hbk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_bk

theorem czStFourFP_Hc_ka {a b k : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x k a hka r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x k a hka (((v ^ czStFourFP_chi a b k a : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_ka hab hka hkb, zpow_neg_one,
    czStFourFP_H_ka a b k hab hka.symm hkb.symm, mul_comm r]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_ka

theorem czStFourFP_Hc_kb {a b k : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x k b hkb r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x k b hkb (((v ^ czStFourFP_chi a b k b : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_kb hab hka hkb, zpow_one,
    czStFourFP_H_kb a b k hab hka.symm hkb.symm, mul_comm r]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_kb

theorem czStFourFP_Hc_kl {a b k l : I} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (hla : l ≠ a) (hlb : l ≠ b) (hkl : k ≠ l) (v : Rˣ) (r : R) :
    czStFourFP_H a b hab v * SteinbergGroup.x k l hkl r * (czStFourFP_H a b hab v)⁻¹ =
      SteinbergGroup.x k l hkl (((v ^ czStFourFP_chi a b k l : Rˣ) : R) * r) := by
  rw [czStFourFP_chi_kl hka hkb hla hlb, zpow_zero, Units.val_one, one_mul,
    czStFourFP_H_kl a b k l hab hkl hka.symm hkb.symm hla.symm hlb.symm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_Hc_kl

end Cases

/-- **Torus action.**  `H_ab(v)` scales `x_ij` by `v ^ χ_ab(i,j)`. -/
theorem czStFourFP_H_conj (hthird : ∀ a b : I, ∃ k, k ≠ a ∧ k ≠ b) (a b : I) (hab : a ≠ b)
    (v : Rˣ) (i j : I) (hij : i ≠ j) (r : R) :
    czStFourFP_H a b hab v * SteinbergGroup.x i j hij r * (czStFourFP_H a b hab v)⁻¹ =
      SteinbergGroup.x i j hij (((v ^ czStFourFP_chi a b i j : Rˣ) : R) * r) := by
  obtain ⟨k, hka, hkb⟩ := hthird a b
  by_cases hia : i = a
  · subst hia
    by_cases hjb : j = b
    · subst hjb
      exact czStFourFP_Hc_ab hab hka hkb v r
    · exact czStFourFP_Hc_ak hab (Ne.symm hij) hjb hij v r
  · by_cases hib : i = b
    · subst hib
      by_cases hja : j = a
      · subst hja
        exact czStFourFP_Hc_ba hab hka hkb hij v r
      · exact czStFourFP_Hc_bk hab hja (Ne.symm hij) hij v r
    · by_cases hja : j = a
      · subst hja
        exact czStFourFP_Hc_ka hab hia hib v r
      · by_cases hjb : j = b
        · subst hjb
          exact czStFourFP_Hc_kb hab hia hib v r
        · exact czStFourFP_Hc_kl hab hia hib hja hjb hij v r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_conj

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
