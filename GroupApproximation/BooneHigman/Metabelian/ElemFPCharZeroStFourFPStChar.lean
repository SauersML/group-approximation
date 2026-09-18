import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# The torus character and `H_ab(v)` on `x_ab`, `x_ba` (bh-met-91m)

* `czStFourFP_H_ab`, `czStFourFP_H_ba`: `H_ab(v) x_ab(r) H_ab(v)⁻¹ = x_ab(v r v)` and
  `H_ab(v) x_ba(r) H_ab(v)⁻¹ = x_ba(v⁻¹ r v⁻¹)`, given a third index `k`.
* `czStFourFP_chi a b i j = [i=a] - [i=b] - [j=a] + [j=b]`, the exponent with which `H_ab(v)`
  scales `x_ij`, and its seven values.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

/-- Conjugation of a commutator. -/
theorem czStFourFP_conj_commutator {G : Type*} [Group G] (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def, mul_assoc, inv_mul_cancel_left, mul_inv_rev, inv_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_conj_commutator

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

theorem czStFourFP_H_ab (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x a b hab r *
      (czStFourFP_H a b hab v)⁻¹ = SteinbergGroup.x a b hab ((v : R) * r * (v : R)) := by
  have e := SteinbergGroup.x_commutator a k b hak hbk.symm hab r 1
  rw [mul_one] at e
  rw [← e, czStFourFP_conj_commutator, czStFourFP_H_ak a b k hab hak hbk,
    czStFourFP_H_kb a b k hab hak hbk, SteinbergGroup.x_commutator a k b hak hbk.symm hab,
    one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_ab

theorem czStFourFP_H_ba (a b k : I) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (v : Rˣ)
    (r : R) : czStFourFP_H a b hab v * SteinbergGroup.x b a hab.symm r *
      (czStFourFP_H a b hab v)⁻¹ =
        SteinbergGroup.x b a hab.symm (((v⁻¹ : Rˣ) : R) * r * ((v⁻¹ : Rˣ) : R)) := by
  have e := SteinbergGroup.x_commutator b k a hbk hak.symm hab.symm r 1
  rw [mul_one] at e
  rw [← e, czStFourFP_conj_commutator, czStFourFP_H_bk a b k hab hak hbk,
    czStFourFP_H_ka a b k hab hak hbk, SteinbergGroup.x_commutator b k a hbk hak.symm hab.symm,
    one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_H_ba

/-- The character: `H_ab(v)` scales `x_ij` by `v ^ czStFourFP_chi a b i j`. -/
def czStFourFP_chi (a b i j : I) : ℤ :=
  (if i = a then 1 else 0) - (if i = b then 1 else 0) - (if j = a then 1 else 0) +
    (if j = b then 1 else 0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi

section Values

variable {a b k l : I}

theorem czStFourFP_chi_ab (hab : a ≠ b) : czStFourFP_chi a b a b = 2 := by
  rw [czStFourFP_chi, if_pos rfl, if_neg hab, if_neg hab.symm, if_pos rfl]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_ab

theorem czStFourFP_chi_ba (hab : a ≠ b) : czStFourFP_chi a b b a = -2 := by
  rw [czStFourFP_chi, if_neg hab.symm, if_pos rfl, if_pos rfl, if_neg hab]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_ba

theorem czStFourFP_chi_ak (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    czStFourFP_chi a b a k = 1 := by
  rw [czStFourFP_chi, if_pos rfl, if_neg hab, if_neg hka, if_neg hkb]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_ak

theorem czStFourFP_chi_bk (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    czStFourFP_chi a b b k = -1 := by
  rw [czStFourFP_chi, if_neg hab.symm, if_pos rfl, if_neg hka, if_neg hkb]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_bk

theorem czStFourFP_chi_ka (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    czStFourFP_chi a b k a = -1 := by
  rw [czStFourFP_chi, if_neg hka, if_neg hkb, if_pos rfl, if_neg hab]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_ka

theorem czStFourFP_chi_kb (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) :
    czStFourFP_chi a b k b = 1 := by
  rw [czStFourFP_chi, if_neg hka, if_neg hkb, if_neg hab.symm, if_pos rfl]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_kb

theorem czStFourFP_chi_kl (hka : k ≠ a) (hkb : k ≠ b) (hla : l ≠ a) (hlb : l ≠ b) :
    czStFourFP_chi a b k l = 0 := by
  rw [czStFourFP_chi, if_neg hka, if_neg hkb, if_neg hla, if_neg hlb]
  norm_num

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_chi_kl

end Values

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
