import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.InitTail
import Mathlib.Tactic.Abel
import GroupApproximation.Meta.AxiomGuard

/-!
# Top-coefficient linearity of Witt vector sums and products (bh-met-87h, part 5)

Work in `𝕎 R`, the ring of `p`-typical Witt vectors. Split `x = init j x + V^j s` with
`s = (tail j x).shift j` (`eHighWittE_decomp`). Adding `V^j w` changes the `j`-th
coefficient by exactly `w₀` (`eHighWittE_coeff_add_V`). Two consequences follow.

* `(x + y)_j = (init j x + init j y)_j + x_j + y_j` (`eHighWittE_coeff_add`).
* `(a y)_j = (a · init j y)_j + y_j · a₀ ^ p ^ j`, in characteristic `p`
  (`eHighWittE_coeff_mul`).

The first summand in each depends only on the coordinates below `j`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable {p : ℕ} {R : Type*} [Fact p.Prime] [CommRing R]

theorem eHighWittE_init_coeff_lt (x : WittVector p R) {j i : ℕ} (h : i < j) :
    (WittVector.init j x).coeff i = x.coeff i := by
  simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
  exact if_pos h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_init_coeff_lt

theorem eHighWittE_init_coeff_ge (x : WittVector p R) {j i : ℕ} (h : j ≤ i) :
    (WittVector.init j x).coeff i = 0 := by
  simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
  exact if_neg (Nat.not_lt.mpr h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_init_coeff_ge

theorem eHighWittE_tail_coeff_lt (x : WittVector p R) {j i : ℕ} (h : i < j) :
    (WittVector.tail j x).coeff i = 0 := by
  simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
  exact if_neg (Nat.not_le.mpr h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tail_coeff_lt

theorem eHighWittE_tail_coeff_ge (x : WittVector p R) {j i : ℕ} (h : j ≤ i) :
    (WittVector.tail j x).coeff i = x.coeff i := by
  simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
  exact if_pos h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_tail_coeff_ge

/-- `x = init j x + V^j ((tail j x).shift j)`. -/
theorem eHighWittE_decomp (x : WittVector p R) (j : ℕ) :
    x = WittVector.init j x +
      WittVector.verschiebung^[j] ((WittVector.tail j x).shift j) := by
  rw [← WittVector.eq_iterate_verschiebung (x := WittVector.tail j x) (n := j)
    fun i hi => eHighWittE_tail_coeff_lt x hi, WittVector.init_add_tail]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_decomp

theorem eHighWittE_shift_coeff_zero (x : WittVector p R) (j : ℕ) :
    ((WittVector.tail j x).shift j).coeff 0 = x.coeff j := by
  rw [WittVector.shift_coeff, add_zero, eHighWittE_tail_coeff_ge x (le_refl j)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_shift_coeff_zero

/-- **Adding `V^j w` shifts the `j`-th coefficient by `w₀`.** -/
theorem eHighWittE_coeff_add_V (Z w : WittVector p R) (j : ℕ) :
    (Z + WittVector.verschiebung^[j] w).coeff j = Z.coeff j + w.coeff 0 := by
  have hs : WittVector.tail j Z =
      WittVector.verschiebung^[j] ((WittVector.tail j Z).shift j) :=
    WittVector.eq_iterate_verschiebung fun i hi => eHighWittE_tail_coeff_lt Z hi
  have hsum : Z + WittVector.verschiebung^[j] w = WittVector.init j Z +
      WittVector.verschiebung^[j] ((WittVector.tail j Z).shift j + w) := by
    rw [iterate_map_add, ← hs, ← add_assoc, WittVector.init_add_tail]
  have hdis : ∀ n, (WittVector.init j Z).coeff n = 0 ∨
      (WittVector.verschiebung^[j] ((WittVector.tail j Z).shift j + w)).coeff n = 0 := by
    intro n
    rcases Nat.lt_or_ge n j with h | h
    · exact Or.inr (WittVector.iterate_verschiebung_coeff_eq_zero _ h)
    · exact Or.inl (eHighWittE_init_coeff_ge Z h)
  have hV : (WittVector.verschiebung^[j] ((WittVector.tail j Z).shift j + w)).coeff j =
      ((WittVector.tail j Z).shift j + w).coeff 0 := by
    have h0 := WittVector.iterate_verschiebung_coeff ((WittVector.tail j Z).shift j + w) j 0
    rwa [zero_add] at h0
  rw [hsum, WittVector.coeff_add_of_disjoint j _ _ hdis, eHighWittE_init_coeff_ge Z (le_refl j),
    zero_add, hV, WittVector.add_coeff_zero, eHighWittE_shift_coeff_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_coeff_add_V

/-- **Sum.** `(x + y)_j = (init j x + init j y)_j + x_j + y_j`. -/
theorem eHighWittE_coeff_add (x y : WittVector p R) (j : ℕ) :
    (x + y).coeff j = (WittVector.init j x + WittVector.init j y).coeff j +
      x.coeff j + y.coeff j := by
  have h : x + y = WittVector.init j x + WittVector.init j y +
      WittVector.verschiebung^[j] ((WittVector.tail j x).shift j +
        (WittVector.tail j y).shift j) := by
    rw [iterate_map_add]
    conv_lhs => rw [eHighWittE_decomp x j, eHighWittE_decomp y j]
    abel
  rw [h, eHighWittE_coeff_add_V, WittVector.add_coeff_zero, eHighWittE_shift_coeff_zero,
    eHighWittE_shift_coeff_zero, add_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_coeff_add

/-- **Product.** In characteristic `p`,
`(a y)_j = (a · init j y)_j + y_j · a₀ ^ p ^ j`. -/
theorem eHighWittE_coeff_mul [CharP R p] (a y : WittVector p R) (j : ℕ) :
    (a * y).coeff j = (a * WittVector.init j y).coeff j + y.coeff j * a.coeff 0 ^ p ^ j := by
  have h : a * y = a * WittVector.init j y +
      WittVector.verschiebung^[j] ((WittVector.tail j y).shift j) * a := by
    rw [mul_comm _ a, ← mul_add, ← eHighWittE_decomp y j]
  rw [h, WittVector.iterate_verschiebung_mul_left, eHighWittE_coeff_add_V,
    WittVector.mul_coeff_zero, eHighWittE_shift_coeff_zero, WittVector.iterate_frobenius_coeff]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_coeff_mul

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
