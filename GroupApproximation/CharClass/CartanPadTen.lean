import GroupApproximation.CharClass.CartanMidFourChain

/-!
# The padded tensor generator, and the four slot terms

`cc-steenrod`'s recipe, which is what every degree cast in their lane was removed
by: **never let a degree be an expression in the inputs**.  Carry every degree as
a free parameter and absorb the constraint into a constructor that returns `0`
off the diagonal.

That is what this file's `padTen` is.  Two `padTen`s at the same three degrees
are literally the same term, whatever route produced those degrees, so the
mismatch that blocked the interchange's chain-map property — the same number
spelled `a + 1 + b` on one side and `(a + b) + 1` on the other, propositionally
but not definitionally equal — never arises, because neither side spells a sum
at all.

The four slot terms are then the four per-slot boundaries of a nested tensor,
each a dependent match on its own degree so that "this slot has a boundary"
is visible in the type, with every degree of the *result* a parameter.

## Main results

* `padTen` — the tensor generator with all three degrees free.
* `slotOne`, `slotTwo`, `slotThree`, `slotFour` — the four terms.
-/

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The padded generator -/

/-- The decomposable `u ⊗ v` placed in total degree `k`, or `0` if the degrees do
not add up.  All three degrees are free parameters, which is the whole point. -/
noncomputable def padTen (A B : FreeCx) (k a b : ℕ)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) : TensorIdx A B k →₀ ZMod 2 :=
  if h : a + b = k then tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) u v else 0

theorem padTen_of_eq (A B : FreeCx) (k a b : ℕ) (h : a + b = k)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    padTen A B k a b u v = tenElt A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) u v :=
  dif_pos h

theorem padTen_of_ne (A B : FreeCx) (k a b : ℕ) (h : ¬ a + b = k)
    (u : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    padTen A B k a b u v = 0 :=
  dif_neg h

theorem padTen_zero_left (A B : FreeCx) (k a b : ℕ)
    (v : B.ι b →₀ ZMod 2) : padTen A B k a b (0 : A.ι a →₀ ZMod 2) v = 0 := by
  by_cases h : a + b = k
  · rw [padTen_of_eq A B k a b h]
    exact tenElt_zero_left A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) v
  · exact padTen_of_ne A B k a b h 0 v

theorem padTen_zero_right (A B : FreeCx) (k a b : ℕ)
    (u : A.ι a →₀ ZMod 2) : padTen A B k a b u (0 : B.ι b →₀ ZMod 2) = 0 := by
  by_cases h : a + b = k
  · rw [padTen_of_eq A B k a b h]
    exact tenElt_zero_right A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) u
  · exact padTen_of_ne A B k a b h u 0

theorem padTen_add_left (A B : FreeCx) (k a b : ℕ)
    (u u' : A.ι a →₀ ZMod 2) (v : B.ι b →₀ ZMod 2) :
    padTen A B k a b (u + u') v = padTen A B k a b u v + padTen A B k a b u' v := by
  by_cases h : a + b = k
  · rw [padTen_of_eq A B k a b h, padTen_of_eq A B k a b h, padTen_of_eq A B k a b h]
    exact tenElt_add_left A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) u u' v
  · rw [padTen_of_ne A B k a b h, padTen_of_ne A B k a b h, padTen_of_ne A B k a b h]
    exact (add_zero 0).symm

theorem padTen_add_right (A B : FreeCx) (k a b : ℕ)
    (u : A.ι a →₀ ZMod 2) (v v' : B.ι b →₀ ZMod 2) :
    padTen A B k a b u (v + v') = padTen A B k a b u v + padTen A B k a b u v' := by
  by_cases h : a + b = k
  · rw [padTen_of_eq A B k a b h, padTen_of_eq A B k a b h, padTen_of_eq A B k a b h]
    exact tenElt_add_right A B (⟨(a, b), h⟩ : Steenrod.PairDeg k) u v v'
  · rw [padTen_of_ne A B k a b h, padTen_of_ne A B k a b h, padTen_of_ne A B k a b h]
    exact (add_zero 0).symm

/-! ## 2. The four slot terms -/

variable (A B C D : FreeCx)

/-- The boundary in the first slot, regrouped.  The three degrees of the result
are parameters; only the input degree of the differentiated slot is matched on. -/
noncomputable def slotOne (k e1 e2 : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) →
      (C.ι a3 →₀ ZMod 2) → (D.ι a4 →₀ ZMod 2) →
      (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | 0, _, _, _, _, _, _, _ => 0
  | m + 1, a2, a3, a4, w1, w2, w3, w4 =>
      padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
        (padTen A C e1 m a3 (A.d m w1) w3)
        (padTen B D e2 a2 a4 w2 w4)

/-- The boundary in the second slot, regrouped. -/
noncomputable def slotTwo (k e1 e2 : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) →
      (C.ι a3 →₀ ZMod 2) → (D.ι a4 →₀ ZMod 2) →
      (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | _, 0, _, _, _, _, _, _ => 0
  | a1, m + 1, a3, a4, w1, w2, w3, w4 =>
      padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
        (padTen A C e1 a1 a3 w1 w3)
        (padTen B D e2 m a4 (B.d m w2) w4)

/-- The boundary in the third slot, regrouped. -/
noncomputable def slotThree (k e1 e2 : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) →
      (C.ι a3 →₀ ZMod 2) → (D.ι a4 →₀ ZMod 2) →
      (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | _, _, 0, _, _, _, _, _ => 0
  | a1, a2, m + 1, a4, w1, w2, w3, w4 =>
      padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
        (padTen A C e1 a1 m w1 (C.d m w3))
        (padTen B D e2 a2 a4 w2 w4)

/-- The boundary in the fourth slot, regrouped. -/
noncomputable def slotFour (k e1 e2 : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) →
      (C.ι a3 →₀ ZMod 2) → (D.ι a4 →₀ ZMod 2) →
      (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | _, _, _, 0, _, _, _, _ => 0
  | a1, a2, a3, m + 1, w1, w2, w3, w4 =>
      padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
        (padTen A C e1 a1 a3 w1 w3)
        (padTen B D e2 a2 m w2 (D.d m w4))

end

end GroupApproximation.CharClass
