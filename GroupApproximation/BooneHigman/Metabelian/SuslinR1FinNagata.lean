import Mathlib.RingTheory.NoetherNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# R1, finite form: Nagata's change of variables

Lane `bh-met-90r`.  Over a field `k`, every nonzero `g ∈ k[s_0,…,s_{n-1}][X]` is sent by some
ring automorphism of `k[s_0,…,s_{n-1}][X]` to a polynomial in `X` with a UNIT leading
coefficient (`suslinR1Fin_nagata`).  This is the "monic trick" input of Suslin's argument.

The lemmas of the section `equivT` are a verbatim copy of the proof by Nagata in Mathlib's
`Mathlib/RingTheory/NoetherNormalization.lean` (Copyright (c) 2025 Sihan Su; Apache 2.0;
authors Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su), where they are `private`.  Only the
names are changed (prefix `suslinR1Fin`) and `private` is dropped; the proofs are unchanged.
The automorphism `suslinR1FinT f` of `k[X_0,…,X_n]` maps `X_i` to `X_i + X_0 ^ (up ^ i)` for
`i ≠ 0`, where `up = 2 + totalDegree f`, and makes the leading coefficient of `f` in `X_0` a
unit (`suslinR1Fin_T_leadingcoeff_isUnit`).  Transport along `finSuccEquiv` gives the endpoint.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

section equivT

-- Mathlib's lakefile builds the original proofs with this option (core default: 1).
set_option maxSynthPendingDepth 3

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
theorem suslinR1Fin_lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_lt_up

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The algebra map `suslinR1FinT1 f c` maps `X_i` into `X_i + c • X_0 ^ r_i` when `i ≠ 0`
and `X_0` to `X_0`. -/
noncomputable abbrev suslinR1FinT1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1FinT1

theorem suslinR1Fin_t1_comp_t1_neg (c : k) :
    (suslinR1FinT1 f c).comp (suslinR1FinT1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_t1_comp_t1_neg

/-- `suslinR1FinT1 f 1` leads to an algebra equiv `suslinR1FinT f`. -/
noncomputable abbrev suslinR1FinT :=
  AlgEquiv.ofAlgHom (suslinR1FinT1 f 1) (suslinR1FinT1 f (-1))
    (suslinR1Fin_t1_comp_t1_neg f 1) (by simpa using suslinR1Fin_t1_comp_t1_neg f (-1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1FinT

theorem suslinR1Fin_sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (suslinR1Fin_lt_up vlt) (suslinR1Fin_lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_sum_r_mul_ne

theorem suslinR1Fin_degreeOf_zero_t {a : k} (ha : a ≠ 0) :
    ((suslinR1FinT f) (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_degreeOf_zero_t

/-- `suslinR1FinT` maps different monomials of `f` to polynomials with different degrees in
`X_0`. -/
theorem suslinR1Fin_degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support)
    (ne : v ≠ w) :
    (suslinR1FinT f <| monomial v <| coeff v f).degreeOf 0 ≠
    (suslinR1FinT f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [suslinR1Fin_degreeOf_zero_t _ _ <| mem_support_iff.mp hv,
    suslinR1Fin_degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine suslinR1Fin_sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_degreeOf_t_ne_of_ne

theorem suslinR1Fin_leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((suslinR1FinT f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((suslinR1FinT1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_leadingCoeff_finSuccEquiv_t

/-- `suslinR1FinT` maps `f` into some polynomial in `X_0` such that the leading coefficient is
invertible. -/
theorem suslinR1Fin_T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (suslinR1FinT f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (suslinR1FinT f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((suslinR1FinT f) (h x))).degree <
      (finSuccEquiv k n ((suslinR1FinT f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using suslinR1Fin_degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff :
      (finSuccEquiv k n ((suslinR1FinT f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((suslinR1FinT f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((suslinR1FinT f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [suslinR1Fin_leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_T_leadingcoeff_isUnit

end equivT

/-- **Nagata's change of variables, one-variable form.**  Over a field `k`, every nonzero
`g ∈ k[s_0,…,s_{n-1}][X]` is sent by some ring automorphism of `k[s_0,…,s_{n-1}][X]` to a
polynomial whose leading coefficient in `X` is a unit. -/
theorem suslinR1Fin_nagata (g : Polynomial (MvPolynomial (Fin n) k)) (hg : g ≠ 0) :
    ∃ φ : Polynomial (MvPolynomial (Fin n) k) ≃+* Polynomial (MvPolynomial (Fin n) k),
      IsUnit (φ g).leadingCoeff := by
  have hf : (finSuccEquiv k n).symm g ≠ 0 := by
    intro h
    exact hg (by simpa using congrArg (finSuccEquiv k n) h)
  exact ⟨(((finSuccEquiv k n).symm.trans (suslinR1FinT ((finSuccEquiv k n).symm g))).trans
    (finSuccEquiv k n)).toRingEquiv, suslinR1Fin_T_leadingcoeff_isUnit _ hf⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_nagata

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
