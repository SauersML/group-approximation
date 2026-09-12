import GroupApproximation.CharClass.ParityEvenSlice
import GroupApproximation.CharClass.WuSymmetric

/-!
# The slice polynomial's coefficients are elementary symmetric functions

`sliceClass` records a total Chern class as `∏ (1 + h_j X)^{d_j}`, and the
splitting principle delivers Chern classes as elementary symmetric functions of
the roots.  Those meet at one identity: the `a`-th coefficient of a product of
factors `1 + y_l X` is the `a`-th elementary symmetric function of the `y_l`.

This is Vieta in the *reciprocal* convention.  `Finset.prod_X_add_C_coeff` is the
other one, `∏ (X + y_l)`, where the same symmetric function appears at the
complementary coefficient; neither converts to the other without reversing the
polynomial, so this is proved directly from `esymmOn_insert` instead.

Note what is **not** here.  A product with multiplicities, `∏_j (1 + h_j X)^{d_j}`,
is not of this shape until the exponents are unfolded into a family of linear
factors indexed by a set of size `∑ d_j`.  That reindexing is a separate step and
the multiset it produces is not squarefree.

## Main declarations

* `coeff_prod_one_add_C_mul_X` — **reciprocal Vieta.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open Polynomial

noncomputable section

variable {A σ : Type*} [CommRing A] [DecidableEq σ]

/-- **Reciprocal Vieta.**  The `a`-th coefficient of `∏_{l ∈ s} (1 + y_l X)` is the
`a`-th elementary symmetric function of the `y_l` over `s`. -/
theorem coeff_prod_one_add_C_mul_X (s : Finset σ) (y : σ → A) :
    ∀ a : ℕ, (∏ l ∈ s, (1 + Polynomial.C (y l) * Polynomial.X)).coeff a = esymmOn s y a := by
  induction s using Finset.induction_on with
  | empty =>
      intro a
      cases a with
      | zero => rw [Finset.prod_empty, Polynomial.coeff_one_zero, esymmOn_zero]
      | succ a =>
          rw [Finset.prod_empty, esymmOn_empty_of_pos y (Nat.succ_pos a),
            Polynomial.coeff_one, if_neg (Nat.succ_ne_zero a)]
  | @insert w s hw ih =>
      intro a
      rw [Finset.prod_insert hw, esymmOn_insert hw, add_mul, one_mul,
        Polynomial.coeff_add, ih a]
      congr 1
      rw [mul_assoc, Polynomial.coeff_C_mul]
      congr 1
      cases a with
      | zero =>
          rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul,
            esymmShift_zero]
      | succ a => rw [Polynomial.coeff_X_mul, ih a, esymmShift_succ]

end

end GroupApproximation.CharClass
