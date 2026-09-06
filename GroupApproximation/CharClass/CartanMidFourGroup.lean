import GroupApproximation.CharClass.CartanPadTen

/-!
# Grouping the differential of a fourfold decomposable into the four slots

Both sides of the interchange's chain-map identity are the sum of the same four
slot terms.  This file does the target side: the differential of the interchanged
fourfold, regrouped.

Every degree of the *result* is a parameter here, never a sum of the input
degrees.  That is what makes the two sides comparable: a target degree reached as
`a + 1 + b` on one route and as `(a + b) + 1` on the other is the same parameter
either way, and `padTen` absorbs the equation.

The pattern of every proof below is the same two cases, on the degree of the slot
being differentiated: at degree zero the half-differential and the slot are both
zero, and at a successor both are the same padded generator.

## Main results

* `midSwap_tenElt4''` — the interchange on a decomposable, all degrees free.
* `tenElt_tdL_slotOne`, `tenElt_tdR_slotThree`, `tenElt_tdL_slotTwo`,
  `tenElt_tdR_slotFour` — the four slot identifications.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-! ## 1. The slot terms at zero and at a successor -/

theorem slotOne_zero (k e1 e2 a2 a3 a4 : ℕ)
    (w1 : A.ι 0 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    slotOne A B C D k e1 e2 0 a2 a3 a4 w1 w2 w3 w4 = 0 := rfl

theorem slotOne_succ (k e1 e2 m a2 a3 a4 : ℕ)
    (w1 : A.ι (m + 1) →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    slotOne A B C D k e1 e2 (m + 1) a2 a3 a4 w1 w2 w3 w4
      = padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
          (padTen A C e1 m a3 (A.d m w1) w3)
          (padTen B D e2 a2 a4 w2 w4) := rfl

theorem slotTwo_zero (k e1 e2 a1 a3 a4 : ℕ)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι 0 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    slotTwo A B C D k e1 e2 a1 0 a3 a4 w1 w2 w3 w4 = 0 := rfl

theorem slotTwo_succ (k e1 e2 a1 m a3 a4 : ℕ)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι (m + 1) →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    slotTwo A B C D k e1 e2 a1 (m + 1) a3 a4 w1 w2 w3 w4
      = padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
          (padTen A C e1 a1 a3 w1 w3)
          (padTen B D e2 m a4 (B.d m w2) w4) := rfl

theorem slotThree_zero (k e1 e2 a1 a2 a4 : ℕ)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι 0 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    slotThree A B C D k e1 e2 a1 a2 0 a4 w1 w2 w3 w4 = 0 := rfl

theorem slotThree_succ (k e1 e2 a1 a2 m a4 : ℕ)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι (m + 1) →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    slotThree A B C D k e1 e2 a1 a2 (m + 1) a4 w1 w2 w3 w4
      = padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
          (padTen A C e1 a1 m w1 (C.d m w3))
          (padTen B D e2 a2 a4 w2 w4) := rfl

theorem slotFour_zero (k e1 e2 a1 a2 a3 : ℕ)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι 0 →₀ ZMod 2) :
    slotFour A B C D k e1 e2 a1 a2 a3 0 w1 w2 w3 w4 = 0 := rfl

theorem slotFour_succ (k e1 e2 a1 a2 a3 m : ℕ)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι (m + 1) →₀ ZMod 2) :
    slotFour A B C D k e1 e2 a1 a2 a3 (m + 1) w1 w2 w3 w4
      = padTen (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2
          (padTen A C e1 a1 a3 w1 w3)
          (padTen B D e2 a2 m w2 (D.d m w4)) := rfl

/-! ## 2. The interchange with every degree free -/

/-- `midSwap_tenElt4'` with the two degrees of the result carried as parameters
rather than spelled as sums of the input degrees.  This is the form that lets the
two sides of the chain-map identity meet. -/
theorem midSwap_tenElt4'' (k P Q e1 e2 a1 a2 a3 a4 : ℕ)
    (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2) (he : e1 + e2 = k)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = tenElt (tensorFreeCx A C) (tensorFreeCx B D) (⟨(e1, e2), he⟩ : Steenrod.PairDeg k)
          (tenElt A C (⟨(a1, a3), he1⟩ : Steenrod.PairDeg e1) w1 w3)
          (tenElt B D (⟨(a2, a4), he2⟩ : Steenrod.PairDeg e2) w2 w4) := by
  subst he1
  subst he2
  exact midSwap_tenElt4' A B C D k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4

/-! ## 3. The four slot identifications, target side -/

/-- Differentiating the first factor of the left half is the first slot. -/
theorem tenElt_tdL_slotOne (k E e2 a1 a2 a3 a4 : ℕ)
    (hE : E + e2 = k) (he1 : a1 + a3 = E + 1) (he2 : a2 + a4 = e2)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tenElt (tensorFreeCx A C) (tensorFreeCx B D) (⟨(E, e2), hE⟩ : Steenrod.PairDeg k)
        (tdL A C E a1 a3 he1 w1 w3)
        (tenElt B D (⟨(a2, a4), he2⟩ : Steenrod.PairDeg e2) w2 w4)
      = slotOne A B C D k E e2 a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a1 with
  | zero => rw [tdL_zero, tenElt_zero_left, slotOne_zero]
  | succ m =>
      rw [tdL_succ, slotOne_succ,
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k E e2 hE,
        padTen_of_eq A C E m a3 (by omega), padTen_of_eq B D e2 a2 a4 he2]

/-- Differentiating the second factor of the left half is the third slot. -/
theorem tenElt_tdR_slotThree (k E e2 a1 a2 a3 a4 : ℕ)
    (hE : E + e2 = k) (he1 : a1 + a3 = E + 1) (he2 : a2 + a4 = e2)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tenElt (tensorFreeCx A C) (tensorFreeCx B D) (⟨(E, e2), hE⟩ : Steenrod.PairDeg k)
        (tdR A C E a1 a3 he1 w1 w3)
        (tenElt B D (⟨(a2, a4), he2⟩ : Steenrod.PairDeg e2) w2 w4)
      = slotThree A B C D k E e2 a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a3 with
  | zero => rw [tdR_zero, tenElt_zero_left, slotThree_zero]
  | succ n =>
      rw [tdR_succ, slotThree_succ,
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k E e2 hE,
        padTen_of_eq A C E a1 n (by omega), padTen_of_eq B D e2 a2 a4 he2]

/-- Differentiating the first factor of the right half is the second slot. -/
theorem tenElt_tdL_slotTwo (k e1 G a1 a2 a3 a4 : ℕ)
    (hG : e1 + G = k) (he1 : a1 + a3 = e1) (he2 : a2 + a4 = G + 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tenElt (tensorFreeCx A C) (tensorFreeCx B D) (⟨(e1, G), hG⟩ : Steenrod.PairDeg k)
        (tenElt A C (⟨(a1, a3), he1⟩ : Steenrod.PairDeg e1) w1 w3)
        (tdL B D G a2 a4 he2 w2 w4)
      = slotTwo A B C D k e1 G a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a2 with
  | zero => rw [tdL_zero, tenElt_zero_right, slotTwo_zero]
  | succ m =>
      rw [tdL_succ, slotTwo_succ,
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k e1 G hG,
        padTen_of_eq A C e1 a1 a3 he1, padTen_of_eq B D G m a4 (by omega)]

/-- Differentiating the second factor of the right half is the fourth slot. -/
theorem tenElt_tdR_slotFour (k e1 G a1 a2 a3 a4 : ℕ)
    (hG : e1 + G = k) (he1 : a1 + a3 = e1) (he2 : a2 + a4 = G + 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tenElt (tensorFreeCx A C) (tensorFreeCx B D) (⟨(e1, G), hG⟩ : Steenrod.PairDeg k)
        (tenElt A C (⟨(a1, a3), he1⟩ : Steenrod.PairDeg e1) w1 w3)
        (tdR B D G a2 a4 he2 w2 w4)
      = slotFour A B C D k e1 G a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a4 with
  | zero => rw [tdR_zero, tenElt_zero_right, slotFour_zero]
  | succ n =>
      rw [tdR_succ, slotFour_succ,
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k e1 G hG,
        padTen_of_eq A C e1 a1 a3 he1, padTen_of_eq B D G a2 n (by omega)]

end

end GroupApproximation.CharClass
