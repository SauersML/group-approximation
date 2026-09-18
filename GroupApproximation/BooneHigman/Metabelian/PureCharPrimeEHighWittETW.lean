import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEPad
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittETrunc
import Mathlib.RingTheory.WittVector.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import GroupApproximation.Meta.AxiomGuard

/-!
# Coordinates of `W_e(L)ⁿ` are weight-polynomial (bh-met-87h, part 9)

On `N = W_e(L)ⁿ` use the coordinates `co y (i, j) = (y i)_j` with weights
`w (i, j) = K ^ j` (`eHighWittE_w`, `eHighWittE_co`). Here `K ≥ 1` bounds the total degrees of
the Witt addition and multiplication polynomials of index `< e` (`eHighWittE_K`).

A map `F : N → W_e(L)` is *good* (`eHighWittE_Good`) if every coordinate `(F x)_j` is a
`K ^ j`-padded polynomial function. Good maps are closed under the following.

* Coordinate projections and constants.
* Sums (`eHighWittE_good_add`). The formula
  `(a + b)_j = (init_j a + init_j b)_j + a_j + b_j` (`eHighWittE_coeff_add`) writes the first
  term as `wittAdd_j`, of total degree `≤ K`, evaluated at coordinates of index `< j`. Those
  are `K ^ j / K`-padded.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

variable (p : ℕ) [Fact p.Prime] (e : ℕ)

/-- A bound for the total degrees of `wittAdd p j` and `wittMul p j`, `j < e`. -/
def eHighWittE_K : ℕ :=
  1 + ∑ j ∈ Finset.range e,
    ((WittVector.wittAdd p j).totalDegree + (WittVector.wittMul p j).totalDegree)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_K

theorem eHighWittE_K_pos : 0 < eHighWittE_K p e :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_K_pos

theorem eHighWittE_sum_le {j : ℕ} (hj : j < e) :
    (WittVector.wittAdd p j).totalDegree + (WittVector.wittMul p j).totalDegree ≤
      eHighWittE_K p e :=
  le_trans (Finset.single_le_sum
      (f := fun j => (WittVector.wittAdd p j).totalDegree + (WittVector.wittMul p j).totalDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))
    (Nat.le_add_left _ 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_sum_le

theorem eHighWittE_add_le {j : ℕ} (hj : j < e) :
    (WittVector.wittAdd p j).totalDegree ≤ eHighWittE_K p e :=
  le_trans (Nat.le_add_right _ _) (eHighWittE_sum_le p e hj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_add_le

theorem eHighWittE_mul_le {j : ℕ} (hj : j < e) :
    (WittVector.wittMul p j).totalDegree ≤ eHighWittE_K p e :=
  le_trans (Nat.le_add_left _ _) (eHighWittE_sum_le p e hj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_mul_le

variable (L : Type) [Field L] (n : ℕ)

/-- Weights: coordinate `(i, j)` has weight `K ^ j`. -/
def eHighWittE_w : Fin n × Fin e → ℕ := fun v => eHighWittE_K p e ^ (v.2 : ℕ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_w

/-- Coordinates of `W_e(L)ⁿ`. -/
def eHighWittE_co : (Fin n → TruncatedWittVector p e L) → Fin n × Fin e → L :=
  fun y v => (y v.1).coeff v.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_co

theorem eHighWittE_co_injective : Function.Injective (eHighWittE_co p e L n) :=
  fun _ _ h => funext fun i => TruncatedWittVector.ext fun j => congrFun h (i, j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_co_injective

/-- `F` is good: its `j`-th coordinate is a `K ^ j`-padded polynomial function. -/
def eHighWittE_Good (F : (Fin n → TruncatedWittVector p e L) → TruncatedWittVector p e L) :
    Prop :=
  ∀ j : Fin e, eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
    (eHighWittE_K p e ^ (j : ℕ)) (fun x => (F x).coeff j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_Good

variable {p e L n}

theorem eHighWittE_good_of_eq {F G : (Fin n → TruncatedWittVector p e L) →
    TruncatedWittVector p e L} (hF : eHighWittE_Good p e L n F) (h : ∀ x, F x = G x) :
    eHighWittE_Good p e L n G :=
  fun j => eHighWittE_pad_of_eq (hF j) fun x => by rw [h x]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_of_eq

theorem eHighWittE_good_const (c : TruncatedWittVector p e L) :
    eHighWittE_Good p e L n (fun _ => c) :=
  fun j => eHighWittE_pad_const _ (c.coeff j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_const

theorem eHighWittE_good_coord (i : Fin n) : eHighWittE_Good p e L n (fun x => x i) :=
  fun j => eHighWittE_pad_coord (i, j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_coord

/-- The coordinates of `init j (F x)` are `K ^ j / K`-padded. -/
theorem eHighWittE_good_init {F : (Fin n → TruncatedWittVector p e L) →
    TruncatedWittVector p e L} (hF : eHighWittE_Good p e L n F) (j : Fin e) (k : ℕ) :
    eHighWittE_Pad (eHighWittE_w p e n) (eHighWittE_co p e L n)
      (eHighWittE_K p e ^ (j : ℕ) / eHighWittE_K p e)
      (fun x => (WittVector.init j (F x).out).coeff k) := by
  rcases Nat.lt_or_ge k j with h | h
  · have hk : k < e := lt_trans h j.2
    refine eHighWittE_pad_mono (eHighWittE_pad_of_eq (hF ⟨k, hk⟩) fun x => ?_) ?_
    · rw [eHighWittE_init_coeff_lt _ h]
      exact (TruncatedWittVector.coeff_out (F x) ⟨k, hk⟩).symm
    · rw [Nat.le_div_iff_mul_le (eHighWittE_K_pos p e), ← pow_succ]
      exact Nat.pow_le_pow_right (eHighWittE_K_pos p e) h
  · exact eHighWittE_pad_of_eq (eHighWittE_pad_const _ 0) fun _ =>
      (eHighWittE_init_coeff_ge _ h).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_good_init

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
