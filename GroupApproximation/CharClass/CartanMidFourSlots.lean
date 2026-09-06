import GroupApproximation.CharClass.CartanMidFourChain

/-!
# The four slot terms of the fourfold differential

The differential of a nested tensor is the sum of the four per-slot boundaries,
with no signs, and the middle-four interchange does not touch the slots.  So both
sides of the interchange's chain-map property are the same four terms, grouped
differently.

This file names those four terms and proves the two groupings.  Naming them is
what makes the proof tractable: each slot is a dependent match on its own degree,
each grouping lemma splits only the two degrees it needs, and the structure
projection of `tensorFreeCx` never appears, because the only route to the outer
half is `tdL_nested`, which spent it once.

The four grouping lemmas are not proved yet.  What blocks them is not the
mathematics, which is a term-by-term matching, but that the two sides spell the
same degree two ways: after splitting `a₁` and `a₃`, one side carries
`a₁' + 1 + a₃` and the other `(a₁' + a₃) + 1`, and no ordinary normalisation
lemma bridges those, because the successor is written as an addition rather than
as `Nat.succ`.  Closing the gap by definitional equality is not an option
either: any such check unfolds the tensor's structure literal and exceeds the
budget.  The next attempt should carry the post-differential degree as an
explicit parameter rather than compute it, so that both sides are built from the
same expression and no normalisation is needed.

## Main results

* `slotOne`, `slotTwo`, `slotThree`, `slotFour` — the four terms of the
  differential of a nested tensor, regrouped.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-! ## 1. The four slot terms -/

/-- The boundary in the first slot, regrouped. -/
noncomputable def slotOne (k : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), a1 + a2 + (a3 + a4) = k + 1 →
      (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) → (C.ι a3 →₀ ZMod 2) →
      (D.ι a4 →₀ ZMod 2) → (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | 0, _, _, _, _, _, _, _, _ => 0
  | a1' + 1, a2, a3, a4, h, w1, w2, w3, w4 =>
      tenElt (tensorFreeCx A C) (tensorFreeCx B D)
        (⟨(a1' + a3, a2 + a4), by omega⟩ : Steenrod.PairDeg k)
        (tenElt A C (⟨(a1', a3), rfl⟩ : Steenrod.PairDeg (a1' + a3)) (A.d a1' w1) w3)
        (tenElt B D (⟨(a2, a4), rfl⟩ : Steenrod.PairDeg (a2 + a4)) w2 w4)

/-- The boundary in the second slot, regrouped. -/
noncomputable def slotTwo (k : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), a1 + a2 + (a3 + a4) = k + 1 →
      (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) → (C.ι a3 →₀ ZMod 2) →
      (D.ι a4 →₀ ZMod 2) → (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | _, 0, _, _, _, _, _, _, _ => 0
  | a1, a2' + 1, a3, a4, h, w1, w2, w3, w4 =>
      tenElt (tensorFreeCx A C) (tensorFreeCx B D)
        (⟨(a1 + a3, a2' + a4), by omega⟩ : Steenrod.PairDeg k)
        (tenElt A C (⟨(a1, a3), rfl⟩ : Steenrod.PairDeg (a1 + a3)) w1 w3)
        (tenElt B D (⟨(a2', a4), rfl⟩ : Steenrod.PairDeg (a2' + a4)) (B.d a2' w2) w4)

/-- The boundary in the third slot, regrouped. -/
noncomputable def slotThree (k : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), a1 + a2 + (a3 + a4) = k + 1 →
      (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) → (C.ι a3 →₀ ZMod 2) →
      (D.ι a4 →₀ ZMod 2) → (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | _, _, 0, _, _, _, _, _, _ => 0
  | a1, a2, a3' + 1, a4, h, w1, w2, w3, w4 =>
      tenElt (tensorFreeCx A C) (tensorFreeCx B D)
        (⟨(a1 + a3', a2 + a4), by omega⟩ : Steenrod.PairDeg k)
        (tenElt A C (⟨(a1, a3'), rfl⟩ : Steenrod.PairDeg (a1 + a3')) w1 (C.d a3' w3))
        (tenElt B D (⟨(a2, a4), rfl⟩ : Steenrod.PairDeg (a2 + a4)) w2 w4)

/-- The boundary in the fourth slot, regrouped. -/
noncomputable def slotFour (k : ℕ) :
    ∀ (a1 a2 a3 a4 : ℕ), a1 + a2 + (a3 + a4) = k + 1 →
      (A.ι a1 →₀ ZMod 2) → (B.ι a2 →₀ ZMod 2) → (C.ι a3 →₀ ZMod 2) →
      (D.ι a4 →₀ ZMod 2) → (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2)
  | _, _, _, 0, _, _, _, _, _ => 0
  | a1, a2, a3, a4' + 1, h, w1, w2, w3, w4 =>
      tenElt (tensorFreeCx A C) (tensorFreeCx B D)
        (⟨(a1 + a3, a2 + a4'), by omega⟩ : Steenrod.PairDeg k)
        (tenElt A C (⟨(a1, a3), rfl⟩ : Steenrod.PairDeg (a1 + a3)) w1 w3)
        (tenElt B D (⟨(a2, a4'), rfl⟩ : Steenrod.PairDeg (a2 + a4')) w2 (D.d a4' w4))

end

end GroupApproximation.CharClass
