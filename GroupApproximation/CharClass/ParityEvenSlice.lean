import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import GroupApproximation.CharClass.WuSymmetric

/-!
# The slice class `∏_j (1 + h_j)^{d_j}` and its even support

Over the slice `{1} × S⁵ × Y` of the mapping torus the bundle `W` restricts to
`V = 1^k ⊕ ⨁_j L_j^{⊕ d_j}`, whose total mod-2 Chern class is

```text
A = ∏_j (1 + h_j)^{d_j} ∈ H^*(Y; F₂),      Y = ∏_j CP^{d_j}, |h_j| = 2.
```

This file records the two properties of the sequence of graded components of `A`
that the parity argument of `ParityEven.lean` consumes, and nothing else:

* `A_q = 0` for **odd** `q`, whenever every `d_j` is even.  The reason is
  Frobenius: `(1 + h_j)^{d_j}` is the square of `(1 + h_j)^{d_j/2}`, hence so is
  `A`, and in characteristic two the odd-degree part of a square vanishes
  because the antidiagonal pairing `p ↔ q - p` has no fixed point.
* `A_q = 0` for `q > ∑_j d_j`, because `A` has degree at most `∑_j d_j`.

**Note on the hypothesis.**  The design source (`stw59-obstruction-lean-routes`
§9) asks for each `d_j` to be a *power of two*, because its induction restricts
to sub-products and needs `A_q` to be a single squarefree monomial `μ_S`.  The
argument in `ParityEven.lean` does not restrict to sub-products and needs only
the two facts above, so **`d_j` even is enough** — this is recorded in
`notes/lix-lane-reports/cc-wu.md`.

The class is carried as a `Polynomial R` in a bookkeeping variable that records
the *index* (cohomological degree halved): `sliceClass` has `A_q` as its `q`-th
coefficient.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open Finset

section Slice

variable {R : Type*} [CommRing R] {J : Type*}

/-- In characteristic two the odd coefficients of a square vanish. -/
theorem coeff_mul_self_odd_eq_zero (h2 : (2 : R) = 0) (p : Polynomial R) {n : ℕ}
    (hn : Odd n) : (p * p).coeff n = 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_antidiagonal_self_eq_zero h2 (fun k => p.coeff k) hn

/-- The total mod-2 Chern class `∏_j (1 + h_j)^{d_j}` of the slice bundle, recorded
as a polynomial in a bookkeeping variable whose `q`-th coefficient is the
degree-`2q` component. -/
noncomputable def sliceClass (u : Finset J) (h : J → R) (d : J → ℕ) : Polynomial R :=
  ∏ j ∈ u, (1 + Polynomial.C (h j) * Polynomial.X) ^ d j

theorem sliceClass_def (u : Finset J) (h : J → R) (d : J → ℕ) :
    sliceClass u h d = ∏ j ∈ u, (1 + Polynomial.C (h j) * Polynomial.X) ^ d j := rfl

theorem sliceClass_coeff_zero (u : Finset J) (h : J → R) (d : J → ℕ) :
    (sliceClass u h d).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, sliceClass_def]
  simp

/-- Every even exponent makes the slice class a square. -/
theorem sliceClass_eq_mul_self (u : Finset J) (h : J → R) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j)) :
    sliceClass u h d
      = (∏ j ∈ u, (1 + Polynomial.C (h j) * Polynomial.X) ^ (d j / 2))
        * ∏ j ∈ u, (1 + Polynomial.C (h j) * Polynomial.X) ^ (d j / 2) := by
  rw [sliceClass_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  obtain ⟨m, hm⟩ := hd j hj
  rw [← pow_add, hm, show (m + m) / 2 = m from by omega]

/-- **Frobenius evenness of the slice class.**  If every `d_j` is even then the
odd-index components of `∏_j (1 + h_j)^{d_j}` vanish. -/
theorem sliceClass_coeff_odd_eq_zero (h2 : (2 : R) = 0) (u : Finset J) (h : J → R) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j)) {q : ℕ} (hq : Odd q) :
    (sliceClass u h d).coeff q = 0 := by
  rw [sliceClass_eq_mul_self u h d hd]
  exact coeff_mul_self_odd_eq_zero h2 _ hq

theorem natDegree_one_add_C_mul_X_le (a : R) :
    (1 + Polynomial.C a * Polynomial.X : Polynomial R).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp

theorem natDegree_sliceClass_le (u : Finset J) (h : J → R) (d : J → ℕ) :
    (sliceClass u h d).natDegree ≤ ∑ j ∈ u, d j := by
  rw [sliceClass_def]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  calc d j * (1 + Polynomial.C (h j) * Polynomial.X : Polynomial R).natDegree
      ≤ d j * 1 := Nat.mul_le_mul le_rfl (natDegree_one_add_C_mul_X_le (h j))
    _ = d j := mul_one _

/-- The slice class vanishes above the top index `∑_j d_j`. -/
theorem sliceClass_coeff_eq_zero_of_lt (u : Finset J) (h : J → R) (d : J → ℕ) {q : ℕ}
    (hq : ∑ j ∈ u, d j < q) : (sliceClass u h d).coeff q = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_sliceClass_le u h d) hq)

/-- A sum of even natural numbers is even. -/
theorem even_sum_of_forall_even (d : J → ℕ) :
    ∀ u : Finset J, (∀ j ∈ u, Even (d j)) → Even (∑ j ∈ u, d j) := by
  intro u
  induction u using Finset.cons_induction with
  | empty => intro _; simp
  | cons a v _ ihv =>
    intro hall
    rw [Finset.sum_cons]
    obtain ⟨p, hp⟩ := hall a (by simp)
    obtain ⟨q, hq⟩ := ihv fun j hj => hall j (by simp [hj])
    exact ⟨p + q, by omega⟩

end Slice

end GroupApproximation.CharClass
