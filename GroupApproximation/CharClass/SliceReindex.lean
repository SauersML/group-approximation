import GroupApproximation.CharClass.SliceBlocks

/-!
# Flattening the block index to a range

The splitting principle consumes a family indexed by `Finset.range r`, one linear
factor per line bundle.  `cc-lix-odd`'s bundle is indexed by
`Fin 3 ⊕ Σ j, Fin (dd j)`: three trivial summands, and then for each projective
factor `j` a block of `dd j` copies of **the same** tautological line.  That
multiplicity is the point.  A reading with one line per factor would put the
elementary symmetric functions in the wrong variables, and the mistake would not
surface until the slice value disagreed.

Two steps, both generic.  A product or sum over `Finset.range r` is one over any
fintype of that cardinality, along an equivalence; and a product over the block
index splits into the trivial part, which contributes `1`, and one power per
factor, which is `sliceClass`.

## Main declarations

* `prod_range_of_equiv`, `sum_range_of_equiv` — flattening along an equivalence.
* `prod_blocks_eq_sliceClass` — **the block product is the slice polynomial.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open Polynomial

noncomputable section

/-! ## 1. Flattening along an equivalence -/

theorem prod_range_of_equiv {M : Type*} [CommMonoid M] {κ : Type*} [Fintype κ] (r : ℕ)
    (e : κ ≃ Fin r) (f : κ → M) (g : ℕ → M)
    (hg : ∀ k : κ, g ((e k) : ℕ) = f k) :
    (∏ l ∈ Finset.range r, g l) = ∏ k : κ, f k := by
  rw [← Fin.prod_univ_eq_prod_range (fun l => g l) r, ← Equiv.prod_comp e (fun i => g (i : ℕ))]
  exact Finset.prod_congr rfl fun k _ => hg k

theorem sum_range_of_equiv {M : Type*} [AddCommMonoid M] {κ : Type*} [Fintype κ] (r : ℕ)
    (e : κ ≃ Fin r) (f : κ → M) (g : ℕ → M)
    (hg : ∀ k : κ, g ((e k) : ℕ) = f k) :
    (∑ l ∈ Finset.range r, g l) = ∑ k : κ, f k := by
  rw [← Fin.sum_univ_eq_sum_range (fun l => g l) r, ← Equiv.sum_comp e (fun i => g (i : ℕ))]
  exact Finset.sum_congr rfl fun k _ => hg k

/-! ## 2. The block product is the slice polynomial -/

variable {A : Type*} [CommRing A] {ℓ : ℕ}

/-- **The block product is the slice polynomial.**  The three trivial summands
contribute `1`; each projective factor contributes its generator to the power of
its dimension, because its block carries the same line `dd j` times. -/
theorem prod_blocks_eq_sliceClass (dd : Fin ℓ → ℕ) (gen : Fin ℓ → A)
    (y : Fin 3 ⊕ (Σ j : Fin ℓ, Fin (dd j)) → A)
    (hzero : ∀ i : Fin 3, y (Sum.inl i) = 0)
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

end

end GroupApproximation.CharClass
