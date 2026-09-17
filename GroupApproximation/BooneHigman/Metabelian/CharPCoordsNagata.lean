import Mathlib.RingTheory.NoetherNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagata's change of variables, made public (lane bh-met-03)

Research node `char-p-polynomial-embedding-via-noether-normalization`: "Noether normalization
... makes `A` a finite module over a polynomial subring".  The polynomial-coordinates route of
this lane needs, besides Noether normalization itself, the *first step* of Nagata's proof:

  for a nonzero `F ∈ k[X_0, ..., X_n]` there is a `k`-algebra automorphism `e` of
  `k[X_0, ..., X_n]` such that `e F`, viewed as a polynomial in `X_0` over
  `k[X_1, ..., X_n]`, has a unit leading coefficient.

Mathlib proves exactly this in `Mathlib/RingTheory/NoetherNormalization.lean`, but as the
`private` lemma `NoetherNormalization.T_leadingcoeff_isUnit` (together with the `private`
abbreviation `T`).  This file copies that `equivT` section verbatim (same `open`s, same
proofs), with the `private` modifiers removed, into its own namespace, and packages the
result as `exists_algEquiv_isUnit_leadingCoeff`.

**Route (Mathlib's).** `T` maps `X_i ↦ X_i + X_0 ^ (up ^ i)` for `i ≠ 0`, with
`up = 2 + totalDegree F`; distinct monomials of `F` acquire distinct `X_0`-degrees (base-`up`
digits), so the leading `X_0`-coefficient of `T F` is a nonzero scalar.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

section equivT

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.lt_up

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- We construct an algebra map `T1 f c` which maps `X_i` into `X_i + c • X_0 ^ r_i`
when `i ≠ 0` and `X_0` to `X_0`. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.T1

lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.t1_comp_t1_neg

/-- `T1 f 1` leads to an algebra equiv `T f`. -/
noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.T

lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.sum_r_mul_ne

lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
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

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.degreeOf_zero_t

/-- `T` maps different monomials of `f` to polynomials with different degrees in `X_0`. -/
lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.degreeOf_t_ne_of_ne

lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.leadingCoeff_finSuccEquiv_t

/-- `T` maps `f` into some polynomial in `X_0` such that the leading coefficient is invertible. -/
lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.T_leadingcoeff_isUnit

end equivT

/-- **Nagata's change of variables.**  A nonzero polynomial in `n + 1` variables over a field
becomes, after a `k`-algebra automorphism, a polynomial in `X_0` over `k[X_1, ..., X_n]` with a
unit leading coefficient. -/
theorem exists_algEquiv_isUnit_leadingCoeff (F : MvPolynomial (Fin (n + 1)) k) (hF : F ≠ 0) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      IsUnit (MvPolynomial.finSuccEquiv k n (e F)).leadingCoeff :=
  ⟨T F, T_leadingcoeff_isUnit F hF⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata.exists_algEquiv_isUnit_leadingCoeff

end GroupApproximation.BooneHigman.Metabelian.CharPCoords.Nagata
