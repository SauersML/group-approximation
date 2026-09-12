import GroupApproximation.CharClass.SliceEsymm

/-!
# Constant blocks of a product of linear factors

The splitting principle produces a family of roots indexed by a flat set, one per
line bundle, while `sliceClass` is a product over the projective factors with
exponents.  Matching them is a reindexing of a multiset, and it decomposes into
two facts that do not depend on how the blocks are indexed:

* a block on which the root is constant contributes that factor to a power;
* a block on which the root is zero contributes nothing.

Both are recorded here, so that the reindexing itself is only the bookkeeping of
which index lies in which block.

The zero block is not a special case of the constant one for a reason worth
stating: it is what the three trivial summands of `𝟏³ ⊕ H` contribute, and their
factor is `1`, not `1 + 0 · X` left standing in the product.

## Main declarations

* `prod_one_add_C_mul_X_const` — a constant block is a power.
* `prod_one_add_C_mul_X_zero` — a zero block is `1`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open Polynomial

noncomputable section

variable {A σ : Type*} [CommRing A]

/-- **A constant block is a power.** -/
theorem prod_one_add_C_mul_X_const (s : Finset σ) (y : σ → A) (c : A) (n : ℕ)
    (hy : ∀ l ∈ s, y l = c) (hcard : s.card = n) :
    (∏ l ∈ s, (1 + Polynomial.C (y l) * Polynomial.X))
      = (1 + Polynomial.C c * Polynomial.X) ^ n := by
  rw [Finset.prod_congr rfl (fun l hl => by rw [hy l hl]), Finset.prod_const, hcard]

/-- **A zero block contributes nothing.** -/
theorem prod_one_add_C_mul_X_zero (s : Finset σ) (y : σ → A)
    (hy : ∀ l ∈ s, y l = 0) :
    (∏ l ∈ s, (1 + Polynomial.C (y l) * Polynomial.X)) = 1 := by
  refine Finset.prod_eq_one fun l hl => ?_
  rw [hy l hl, map_zero, zero_mul, add_zero]

end

end GroupApproximation.CharClass
