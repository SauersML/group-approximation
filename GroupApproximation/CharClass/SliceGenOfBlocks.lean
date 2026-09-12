import GroupApproximation.CharClass.SliceReindex

/-!
# The block product is the slice polynomial, at sphere rank `n`

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm.

`SliceReindex.prod_blocks_eq_sliceClass` recognises `sliceClass` in a product of linear factors
indexed by `Fin 3 ⊕ Σ j, Fin (dd j)`: three constant summands contributing `1`, one power per
projective factor.  At sphere rank `n` the trivial summand has `n + 1` lines; nothing else
changes.  Pure algebra over a commutative ring, so the `F₂` and the field slice values share it.

## Main declarations

* `Gen.prod_blocks_eq_sliceClass` — **the block product is the slice polynomial**, at rank `n`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open Polynomial

noncomputable section

namespace Gen

variable {A : Type*} [CommRing A] {ℓ : ℕ}

/-- **The block product is the slice polynomial**, at sphere rank `n`.  The `n + 1` trivial
summands contribute `1`; each projective factor contributes its generator to the power of its
dimension, because its block carries the same line `dd j` times. -/
theorem prod_blocks_eq_sliceClass (n : ℕ) (dd : Fin ℓ → ℕ) (gen : Fin ℓ → A)
    (y : Fin (n + 1) ⊕ (Σ j : Fin ℓ, Fin (dd j)) → A)
    (hzero : ∀ i : Fin (n + 1), y (Sum.inl i) = 0)
    (hgen : ∀ b : Σ j : Fin ℓ, Fin (dd j), y (Sum.inr b) = gen b.1) :
    (∏ k, (1 + Polynomial.C (y k) * Polynomial.X))
      = sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd := by
  rw [Fintype.prod_sum_type,
    prod_one_add_C_mul_X_zero Finset.univ (fun i => y (Sum.inl i)) (fun i _ => hzero i),
    one_mul, Fintype.prod_sigma, sliceClass_def]
  refine Finset.prod_congr rfl fun j _ => ?_
  refine prod_one_add_C_mul_X_const Finset.univ
    (fun i : Fin (dd j) => y (Sum.inr ⟨j, i⟩)) (gen j) (dd j)
    (fun i _ => hgen ⟨j, i⟩) ?_
  rw [Finset.card_univ, Fintype.card_fin]

end Gen

end

end GroupApproximation.CharClass
