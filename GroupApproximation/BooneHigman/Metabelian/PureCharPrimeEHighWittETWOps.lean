import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittETW
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittPolyFun
import GroupApproximation.Meta.AxiomGuard

/-!
# Sums and matrix actions on `W_e(L)ⁿ` are weight-polynomial (bh-met-87h, part 10)

Good maps `N → W_e(L)` (`eHighWittE_Good`) are closed under the following.

* `+` (`eHighWittE_good_add`).
* Left multiplication by a constant, in characteristic `p` (`eHighWittE_good_cmul`). This uses
  `(c y)_j = (c · init_j y)_j + y_j c₀ ^ p ^ j` (`eHighWittE_coeff_mul`).
* Finite sums (`eHighWittE_good_sum`).

Hence translations and every matrix action `x ↦ (∑ₗ U i l * x l)ᵢ` on `W_e(L)ⁿ` are
weight-polynomial. So `eHighWitt_exists_polyFun_of_weightPoly` gives an invariant, separating,
finite-dimensional space of functions (`eHighWittE_tw_polyFun`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

variable {p : ℕ} [Fact p.Prime] {e : ℕ} {L : Type} [Field L] {n : ℕ}

theorem eHighWittE_good_add {F G : (Fin n → TruncatedWittVector p e L) →
    TruncatedWittVector p e L} (hF : eHighWittE_Good p e L n F)
    (hG : eHighWittE_Good p e L n G) : eHighWittE_Good p e L n (fun x => F x + G x) := by
  intro j
  have hsub : ∀ t : Fin 2 × ℕ, eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ) / eHighWittE_K p e) (fun x => Function.uncurry
        ![(WittVector.init j (F x).out).coeff, (WittVector.init j (G x).out).coeff] t) := by
    rintro ⟨i, k⟩
    revert i
    exact Fin.forall_fin_two.mpr ⟨eHighWittE_good_init hF j k, eHighWittE_good_init hG j k⟩
  have hdeg : (WittVector.wittAdd p j).totalDegree *
      (eHighWittE_K p e ^ (j : ℕ) / eHighWittE_K p e) ≤ eHighWittE_K p e ^ (j : ℕ) :=
    le_trans (Nat.mul_le_mul_right _ (eHighWittE_add_le p e j.2)) (Nat.mul_div_le _ _)
  have hcF : eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ)) (fun x => (F x).out.coeff j) :=
    eHighWittE_pad_of_eq (hF j) fun x => (TruncatedWittVector.coeff_out (F x) j).symm
  have hcG : eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ)) (fun x => (G x).out.coeff j) :=
    eHighWittE_pad_of_eq (hG j) fun x => (TruncatedWittVector.coeff_out (G x) j).symm
  refine eHighWittE_pad_of_eq (eHighWittE_pad_add (eHighWittE_pad_add
    (eHighWittE_pad_subst (WittVector.wittAdd p j) _ hsub hdeg) hcF) hcG) fun x => ?_
  have h := (eHighWittE_tw_add_coeff (F x) (G x) j).trans
    (eHighWittE_coeff_add (F x).out (G x).out j)
  rw [WittVector.add_coeff] at h
  exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_add

theorem eHighWittE_good_cmul [CharP L p] (c : TruncatedWittVector p e L)
    {G : (Fin n → TruncatedWittVector p e L) → TruncatedWittVector p e L}
    (hG : eHighWittE_Good p e L n G) : eHighWittE_Good p e L n (fun x => c * G x) := by
  intro j
  have hsub : ∀ t : Fin 2 × ℕ, eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ) / eHighWittE_K p e) (fun x => Function.uncurry
        ![c.out.coeff, (WittVector.init j (G x).out).coeff] t) := by
    rintro ⟨i, k⟩
    revert i
    exact Fin.forall_fin_two.mpr
      ⟨eHighWittE_pad_const _ (c.out.coeff k), eHighWittE_good_init hG j k⟩
  have hdeg : (WittVector.wittMul p j).totalDegree *
      (eHighWittE_K p e ^ (j : ℕ) / eHighWittE_K p e) ≤ eHighWittE_K p e ^ (j : ℕ) :=
    le_trans (Nat.mul_le_mul_right _ (eHighWittE_mul_le p e j.2)) (Nat.mul_div_le _ _)
  have hcG : eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ)) (fun x => (G x).out.coeff j) :=
    eHighWittE_pad_of_eq (hG j) fun x => (TruncatedWittVector.coeff_out (G x) j).symm
  have hc : eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ)) (fun x => (G x).out.coeff j * c.out.coeff 0 ^ p ^ (j : ℕ)) :=
    eHighWittE_pad_mono (eHighWittE_pad_mul hcG
      (eHighWittE_pad_const 0 (c.out.coeff 0 ^ p ^ (j : ℕ)))) (add_zero _).le
  refine eHighWittE_pad_of_eq (eHighWittE_pad_add
    (eHighWittE_pad_subst (WittVector.wittMul p j) _ hsub hdeg) hc) fun x => ?_
  have h := (eHighWittE_tw_mul_coeff c (G x) j).trans
    (eHighWittE_coeff_mul c.out (G x).out j)
  rw [WittVector.mul_coeff] at h
  exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_cmul

theorem eHighWittE_good_sum {ι : Type} (s : Finset ι)
    (F : ι → (Fin n → TruncatedWittVector p e L) → TruncatedWittVector p e L)
    (hF : ∀ i ∈ s, eHighWittE_Good p e L n (F i)) :
    eHighWittE_Good p e L n (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact eHighWittE_good_of_eq (eHighWittE_good_const 0) fun x => by rw [Finset.sum_empty]
  | insert a s ha ih =>
    exact eHighWittE_good_of_eq (eHighWittE_good_add (hF a (Finset.mem_insert_self a s))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))) fun x => by
        rw [Finset.sum_insert ha]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_sum

theorem eHighWittE_isWeightPoly_of_good {g : (Fin n → TruncatedWittVector p e L) →
    Fin n → TruncatedWittVector p e L} (h : ∀ i, eHighWittE_Good p e L n (fun x => g x i)) :
    eHighWitt_IsWeightPoly (eHighWittE_w p e n) (eHighWittE_co p e L n) g :=
  eHighWittE_isWeightPoly_of_pad fun v => h v.1 v.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isWeightPoly_of_good

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
