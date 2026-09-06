import GroupApproximation.CharClass.CartanMidFourTgt

/-!
# The source side of the interchange's chain-map identity

The interchange of the differential of a fourfold decomposable is the sum of the
same four slot terms that `tensorD_tenElt_grouped` produced on the target side.

The source groups the four factors as `(A ⊗ B) ⊗ (C ⊗ D)`, so its two halves
contribute slots one and two, and slots three and four; the target grouped them
one and three, two and four.  `add_add_add_comm` is the whole of the difference.

## Main results

* `midSwap_tenElt_tdL_slotOne` and its three siblings — the four slot
  identifications on the source side.
* `midSwap_tdL_grouped`, `midSwap_tdR_grouped` — the two halves.
* `midSwap_tensorD_grouped` — their sum, in the target's order.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-! ## 1. The four slot identifications -/

/-- Differentiating the first factor of the left half is the first slot. -/
theorem midSwap_tenElt_tdL_slotOne (k P' Q f e2 a1 a2 a3 a4 : ℕ)
    (hPQ : P' + Q = k) (h1 : a1 + a2 = P' + 1) (h2 : a3 + a4 = Q)
    (hf : f = a1 + a3 - 1) (he2 : a2 + a4 = e2)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P', Q), hPQ⟩ : Steenrod.PairDeg k)
          (tdL A B P' a1 a2 h1 w1 w2)
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = slotOne A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a1 with
  | zero => rw [tdL_zero, tenElt_zero_left, map_zero, slotOne_zero]
  | succ m =>
      have hf' : f = m + a3 := by omega
      subst hf'
      rw [tdL_succ, slotOne_succ,
        midSwap_tenElt4'' A B C D k P' Q (m + a3) e2 m a2 a3 a4 hPQ (by omega) h2 rfl he2
          (by omega),
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k (m + a3) e2 (by omega),
        padTen_of_eq A C (m + a3) m a3 rfl,
        padTen_of_eq B D e2 a2 a4 he2]

/-- Differentiating the second factor of the left half is the second slot. -/
theorem midSwap_tenElt_tdR_slotTwo (k P' Q e1 g a1 a2 a3 a4 : ℕ)
    (hPQ : P' + Q = k) (h1 : a1 + a2 = P' + 1) (h2 : a3 + a4 = Q)
    (he1 : a1 + a3 = e1) (hg : g = a2 + a4 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P', Q), hPQ⟩ : Steenrod.PairDeg k)
          (tdR A B P' a1 a2 h1 w1 w2)
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = slotTwo A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a2 with
  | zero => rw [tdR_zero, tenElt_zero_left, map_zero, slotTwo_zero]
  | succ m =>
      have hg' : g = m + a4 := by omega
      subst hg'
      rw [tdR_succ, slotTwo_succ,
        midSwap_tenElt4'' A B C D k P' Q e1 (m + a4) a1 m a3 a4 hPQ (by omega) h2 he1 rfl
          (by omega),
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k e1 (m + a4) (by omega),
        padTen_of_eq A C e1 a1 a3 he1,
        padTen_of_eq B D (m + a4) m a4 rfl]

/-- Differentiating the first factor of the right half is the third slot. -/
theorem midSwap_tenElt_tdL_slotThree (k P Q' f e2 a1 a2 a3 a4 : ℕ)
    (hPQ : P + Q' = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q' + 1)
    (hf : f = a1 + a3 - 1) (he2 : a2 + a4 = e2)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P, Q'), hPQ⟩ : Steenrod.PairDeg k)
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tdL C D Q' a3 a4 h2 w3 w4))
      = slotThree A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a3 with
  | zero => rw [tdL_zero, tenElt_zero_right, map_zero, slotThree_zero]
  | succ n =>
      have hf' : f = a1 + n := by omega
      subst hf'
      rw [tdL_succ, slotThree_succ,
        midSwap_tenElt4'' A B C D k P Q' (a1 + n) e2 a1 a2 n a4 hPQ h1 (by omega) rfl he2
          (by omega),
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k (a1 + n) e2 (by omega),
        padTen_of_eq A C (a1 + n) a1 n rfl,
        padTen_of_eq B D e2 a2 a4 he2]

/-- Differentiating the second factor of the right half is the fourth slot. -/
theorem midSwap_tenElt_tdR_slotFour (k P Q' e1 g a1 a2 a3 a4 : ℕ)
    (hPQ : P + Q' = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q' + 1)
    (he1 : a1 + a3 = e1) (hg : g = a2 + a4 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P, Q'), hPQ⟩ : Steenrod.PairDeg k)
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tdR C D Q' a3 a4 h2 w3 w4))
      = slotFour A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases a4 with
  | zero => rw [tdR_zero, tenElt_zero_right, map_zero, slotFour_zero]
  | succ n =>
      have hg' : g = a2 + n := by omega
      subst hg'
      rw [tdR_succ, slotFour_succ,
        midSwap_tenElt4'' A B C D k P Q' e1 (a2 + n) a1 a2 a3 n hPQ h1 (by omega) he1 rfl
          (by omega),
        padTen_of_eq (tensorFreeCx A C) (tensorFreeCx B D) k e1 (a2 + n) (by omega),
        padTen_of_eq A C e1 a1 a3 he1,
        padTen_of_eq B D (a2 + n) a2 n rfl]

/-! ## 2. The two halves -/

/-- The interchange of the left half of the differential is the first slot plus
the second. -/
theorem midSwap_tdL_grouped (k P Q e1 e2 f g a1 a2 a3 a4 : ℕ)
    (h : P + Q = k + 1) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2) (hf : f = e1 - 1) (hg : g = e2 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tdL (tensorFreeCx A B) (tensorFreeCx C D) k P Q h
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = slotOne A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + slotTwo A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases P with
  | zero =>
      have ha1 : a1 = 0 := by omega
      have ha2 : a2 = 0 := by omega
      subst ha1
      subst ha2
      rw [tdL_zero, map_zero, slotOne_zero, slotTwo_zero, add_zero]
  | succ P' =>
      rw [tdL_nested, map_add,
        midSwap_tenElt_tdL_slotOne A B C D k P' Q f e2 a1 a2 a3 a4 (by omega) h1 h2
          (by omega) he2 w1 w2 w3 w4,
        midSwap_tenElt_tdR_slotTwo A B C D k P' Q e1 g a1 a2 a3 a4 (by omega) h1 h2
          he1 (by omega) w1 w2 w3 w4]

/-- The interchange of the right half of the differential is the third slot plus
the fourth. -/
theorem midSwap_tdR_grouped (k P Q e1 e2 f g a1 a2 a3 a4 : ℕ)
    (h : P + Q = k + 1) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2) (hf : f = e1 - 1) (hg : g = e2 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tdR (tensorFreeCx A B) (tensorFreeCx C D) k P Q h
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = slotThree A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + slotFour A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases Q with
  | zero =>
      have ha3 : a3 = 0 := by omega
      have ha4 : a4 = 0 := by omega
      subst ha3
      subst ha4
      rw [tdR_zero, map_zero, slotThree_zero, slotFour_zero, add_zero]
  | succ Q' =>
      rw [tdR_nested, map_add,
        midSwap_tenElt_tdL_slotThree A B C D k P Q' f e2 a1 a2 a3 a4 (by omega) h1 h2
          (by omega) he2 w1 w2 w3 w4,
        midSwap_tenElt_tdR_slotFour A B C D k P Q' e1 g a1 a2 a3 a4 (by omega) h1 h2
          he1 (by omega) w1 w2 w3 w4]

/-! ## 3. The source side -/

/-- **The source side.**  The interchange of the differential of a fourfold
decomposable is the sum of the same four slot terms, in the target's order. -/
theorem midSwap_tensorD_grouped (k P Q e1 e2 f g a1 a2 a3 a4 : ℕ)
    (h : P + Q = k + 1) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2) (hf : f = e1 - 1) (hg : g = e2 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tensorD (tensorFreeCx A B) (tensorFreeCx C D) k
          (tenElt (tensorFreeCx A B) (tensorFreeCx C D)
            (⟨(P, Q), h⟩ : Steenrod.PairDeg (k + 1))
            (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
            (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4)))
      = slotOne A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + slotThree A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + (slotTwo A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4
          + slotFour A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4) := by
  rw [tensorD_tenElt, map_add,
    midSwap_tdL_grouped A B C D k P Q e1 e2 f g a1 a2 a3 a4 h h1 h2 he1 he2 hf hg
      w1 w2 w3 w4,
    midSwap_tdR_grouped A B C D k P Q e1 e2 f g a1 a2 a3 a4 h h1 h2 he1 he2 hf hg
      w1 w2 w3 w4,
    add_add_add_comm]

end

end GroupApproximation.CharClass
