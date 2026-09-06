import GroupApproximation.CharClass.CartanMidFourGroup

/-!
# The target side of the interchange's chain-map identity

The differential of an interchanged fourfold decomposable is the sum of the four
slot terms.  The two halves of the differential contribute slots one and three,
and slots two and four, respectively.

The predecessor degrees are carried as parameters `f` and `g` constrained by
truncated subtraction, `f = e1 - 1` and `g = e2 - 1`, rather than by
`f + 1 = e1`.  With the successor form the statement would be vacuous exactly
when `e1 = 0`, which is a case the chain map needs.

## Main results

* `tdL_target_grouped`, `tdR_target_grouped` — the two halves.
* `tensorD_tenElt_grouped` — their sum.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-- The left half of the differential of an interchanged fourfold decomposable
is the first slot plus the third. -/
theorem tdL_target_grouped (k e1 e2 f a1 a2 a3 a4 : ℕ)
    (he : e1 + e2 = k + 1) (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2) (hf : f = e1 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tdL (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2 he
        (tenElt A C (⟨(a1, a3), he1⟩ : Steenrod.PairDeg e1) w1 w3)
        (tenElt B D (⟨(a2, a4), he2⟩ : Steenrod.PairDeg e2) w2 w4)
      = slotOne A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + slotThree A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases e1 with
  | zero =>
      have ha1 : a1 = 0 := by omega
      have ha3 : a3 = 0 := by omega
      subst ha1
      subst ha3
      rw [tdL_zero, slotOne_zero, slotThree_zero, add_zero]
  | succ E =>
      have hf' : f = E := by omega
      subst hf'
      rw [tdL_succ, tensorFreeCx_d, tensorD_tenElt, tenElt_add_left,
        tenElt_tdL_slotOne, tenElt_tdR_slotThree]

/-- The right half of the differential of an interchanged fourfold decomposable
is the second slot plus the fourth. -/
theorem tdR_target_grouped (k e1 e2 g a1 a2 a3 a4 : ℕ)
    (he : e1 + e2 = k + 1) (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2) (hg : g = e2 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tdR (tensorFreeCx A C) (tensorFreeCx B D) k e1 e2 he
        (tenElt A C (⟨(a1, a3), he1⟩ : Steenrod.PairDeg e1) w1 w3)
        (tenElt B D (⟨(a2, a4), he2⟩ : Steenrod.PairDeg e2) w2 w4)
      = slotTwo A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4
        + slotFour A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4 := by
  cases e2 with
  | zero =>
      have ha2 : a2 = 0 := by omega
      have ha4 : a4 = 0 := by omega
      subst ha2
      subst ha4
      rw [tdR_zero, slotTwo_zero, slotFour_zero, add_zero]
  | succ G =>
      have hg' : g = G := by omega
      subst hg'
      rw [tdR_succ, tensorFreeCx_d, tensorD_tenElt, tenElt_add_right,
        tenElt_tdL_slotTwo, tenElt_tdR_slotFour]

/-- **The target side.**  The differential of an interchanged fourfold
decomposable is the sum of the four slot terms. -/
theorem tensorD_tenElt_grouped (k e1 e2 f g a1 a2 a3 a4 : ℕ)
    (he : e1 + e2 = k + 1) (he1 : a1 + a3 = e1) (he2 : a2 + a4 = e2)
    (hf : f = e1 - 1) (hg : g = e2 - 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tensorD (tensorFreeCx A C) (tensorFreeCx B D) k
        (tenElt (tensorFreeCx A C) (tensorFreeCx B D)
          (⟨(e1, e2), he⟩ : Steenrod.PairDeg (k + 1))
          (tenElt A C (⟨(a1, a3), he1⟩ : Steenrod.PairDeg e1) w1 w3)
          (tenElt B D (⟨(a2, a4), he2⟩ : Steenrod.PairDeg e2) w2 w4))
      = slotOne A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + slotThree A B C D k f e2 a1 a2 a3 a4 w1 w2 w3 w4
        + (slotTwo A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4
          + slotFour A B C D k e1 g a1 a2 a3 a4 w1 w2 w3 w4) := by
  rw [tensorD_tenElt,
    tdL_target_grouped A B C D k e1 e2 f a1 a2 a3 a4 he he1 he2 hf w1 w2 w3 w4,
    tdR_target_grouped A B C D k e1 e2 g a1 a2 a3 a4 he he1 he2 hg w1 w2 w3 w4]

end

end GroupApproximation.CharClass
