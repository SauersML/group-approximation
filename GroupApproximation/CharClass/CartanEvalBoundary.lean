import GroupApproximation.CharClass.CartanEvalFour

/-!
# The evaluating functional annihilates boundaries

The comparison is evaluated against a functional that must kill boundaries.  The
differential of the fourfold is the sum of the four per-factor boundaries, the
functional is the product of the four one-slot pairings, and a cocycle pairs to
zero against a boundary in each slot.  So every term of `u ∘ d` has a vanishing
factor.

## Main results

* `singFreeCx_d` — the differential of the singular complex, without forcing the
  structure projection.
* `fourEvalF2_tenElt4_of_left` and its three siblings — one vanishing slot kills
  the product.
* `fourEvalF2_tensorD` — **the functional annihilates boundaries**, given the two
  cocycle conditions.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-- The differential of the singular complex, stated so that nothing has to force
the structure projection. -/
theorem singFreeCx_d (X : TopCat.{0}) (a : ℕ) :
    (singFreeCx X).d a = bdU (ZMod 2) X a := rfl

variable (X : TopCat.{0}) (p q : ℕ)
variable (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)

/-! ## 1. One vanishing slot kills the product -/

section Slots

variable (k P Q a1 a2 a3 a4 : ℕ)
variable (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
variable (w1 : (singFreeCx X).ι a1 →₀ ZMod 2) (w2 : (singFreeCx X).ι a2 →₀ ZMod 2)
variable (w3 : (singFreeCx X).ι a3 →₀ ZMod 2) (w4 : (singFreeCx X).ι a4 →₀ ZMod 2)

/-- The fourfold decomposable, abbreviated. -/
noncomputable def quadElt : TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2 :=
  tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
    (tenElt (singFreeCx X) (singFreeCx X) (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
    (tenElt (singFreeCx X) (singFreeCx X) (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4)

theorem fourEvalF2_quadElt :
    fourEvalF2 X p q α β k (quadElt X k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4)
      = evLin X p α a1 w1 * evLin X q β a2 w2
        * (evLin X p α a3 w3 * evLin X q β a4 w4) :=
  fourEvalF2_tenElt4 X p q α β k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4

theorem fourEvalF2_quadElt_of_one (hw : evLin X p α a1 w1 = 0) :
    fourEvalF2 X p q α β k (quadElt X k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4) = 0 := by
  rw [fourEvalF2_quadElt, hw, zero_mul, zero_mul]

theorem fourEvalF2_quadElt_of_two (hw : evLin X q β a2 w2 = 0) :
    fourEvalF2 X p q α β k (quadElt X k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4) = 0 := by
  rw [fourEvalF2_quadElt, hw, mul_zero, zero_mul]

theorem fourEvalF2_quadElt_of_three (hw : evLin X p α a3 w3 = 0) :
    fourEvalF2 X p q α β k (quadElt X k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4) = 0 := by
  rw [fourEvalF2_quadElt, hw, zero_mul, mul_zero]

theorem fourEvalF2_quadElt_of_four (hw : evLin X q β a4 w4 = 0) :
    fourEvalF2 X p q α β k (quadElt X k P Q a1 a2 a3 a4 h h1 h2 w1 w2 w3 w4) = 0 := by
  rw [fourEvalF2_quadElt, hw, mul_zero, mul_zero]

end Slots

/-! ## 2. The four terms of the differential -/

variable {X p q α β}

theorem fourEvalF2_tdL_inner (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (k P' Q a1 a2 a3 a4 : ℕ) (h1 : a1 + a2 = P' + 1) (h2 : a3 + a4 = Q)
    (hPQ : P' + Q = k) (x1 : (singFreeCx X).ι a1) (x2 : (singFreeCx X).ι a2)
    (x3 : (singFreeCx X).ι a3) (x4 : (singFreeCx X).ι a4) :
    fourEvalF2 X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P', Q), hPQ⟩ : Steenrod.PairDeg k)
          (tdL (singFreeCx X) (singFreeCx X) P' a1 a2 h1
            (Finsupp.single x1 1) (Finsupp.single x2 1))
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q)
            (Finsupp.single x3 1) (Finsupp.single x4 1))) = 0 := by
  cases a1 with
  | zero => rw [tdL_zero, tenElt_zero_left, map_zero]
  | succ a1' =>
      rw [tdL_succ]
      have hw : evLin X p α a1' ((singFreeCx X).d a1' (Finsupp.single x1 1)) = 0 := by
        rw [singFreeCx_d]
        exact evLin_bdU_of_cocycle X p α hα a1' (Finsupp.single x1 1)
      exact fourEvalF2_quadElt_of_one X p q α β k P' Q a1' a2 a3 a4 hPQ (by omega) h2
        ((singFreeCx X).d a1' (Finsupp.single x1 1)) (Finsupp.single x2 1)
        (Finsupp.single x3 1) (Finsupp.single x4 1) hw

theorem fourEvalF2_tdR_inner (hβ : cochainCoboundary (ZMod 2) X q β = 0)
    (k P' Q a1 a2 a3 a4 : ℕ) (h1 : a1 + a2 = P' + 1) (h2 : a3 + a4 = Q)
    (hPQ : P' + Q = k) (x1 : (singFreeCx X).ι a1) (x2 : (singFreeCx X).ι a2)
    (x3 : (singFreeCx X).ι a3) (x4 : (singFreeCx X).ι a4) :
    fourEvalF2 X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P', Q), hPQ⟩ : Steenrod.PairDeg k)
          (tdR (singFreeCx X) (singFreeCx X) P' a1 a2 h1
            (Finsupp.single x1 1) (Finsupp.single x2 1))
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q)
            (Finsupp.single x3 1) (Finsupp.single x4 1))) = 0 := by
  cases a2 with
  | zero => rw [tdR_zero, tenElt_zero_left, map_zero]
  | succ a2' =>
      rw [tdR_succ]
      have hw : evLin X q β a2' ((singFreeCx X).d a2' (Finsupp.single x2 1)) = 0 := by
        rw [singFreeCx_d]
        exact evLin_bdU_of_cocycle X q β hβ a2' (Finsupp.single x2 1)
      exact fourEvalF2_quadElt_of_two X p q α β k P' Q a1 a2' a3 a4 hPQ (by omega) h2
        (Finsupp.single x1 1) ((singFreeCx X).d a2' (Finsupp.single x2 1))
        (Finsupp.single x3 1) (Finsupp.single x4 1) hw

theorem fourEvalF2_tdL_outer (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0) (k P Q : ℕ) (h : P + Q = k + 1)
    (u : (pairFreeCx X).ι P) (v : (pairFreeCx X).ι Q) :
    fourEvalF2 X p q α β k
        (tdL (pairFreeCx X) (pairFreeCx X) k P Q h
          (Finsupp.single u 1) (Finsupp.single v 1)) = 0 := by
  cases P with
  | zero => rw [tdL_zero, map_zero]
  | succ P' =>
      obtain ⟨⟨⟨a1, a2⟩, h1⟩, x1, x2⟩ := u
      obtain ⟨⟨⟨a3, a4⟩, h2⟩, x3, x4⟩ := v
      have hgen : tensorDGen (singFreeCx X) (singFreeCx X) P'
            (⟨⟨(a1, a2), h1⟩, (x1, x2)⟩ :
              TensorIdx (singFreeCx X) (singFreeCx X) (P' + 1))
          = tdL (singFreeCx X) (singFreeCx X) P' a1 a2 h1
              (Finsupp.single x1 1) (Finsupp.single x2 1)
            + tdR (singFreeCx X) (singFreeCx X) P' a1 a2 h1
              (Finsupp.single x1 1) (Finsupp.single x2 1) := rfl
      have hv : (Finsupp.single (⟨⟨(a3, a4), h2⟩, (x3, x4)⟩ :
              TensorIdx (singFreeCx X) (singFreeCx X) Q) (1 : ZMod 2))
          = tenElt (singFreeCx X) (singFreeCx X) (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q)
              (Finsupp.single x3 1) (Finsupp.single x4 1) :=
        (tenElt_single_single (singFreeCx X) (singFreeCx X) _ x3 x4).symm
      rw [tdL_succ, pairFreeCx_d, tensorD_single, one_smul, hgen, hv, tenElt_add_left,
        map_add, fourEvalF2_tdL_inner hα k P' Q a1 a2 a3 a4 h1 h2 (by omega),
        fourEvalF2_tdR_inner hβ k P' Q a1 a2 a3 a4 h1 h2 (by omega), add_zero]

theorem fourEvalF2_tdR_outer (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0) (k P Q : ℕ) (h : P + Q = k + 1)
    (u : (pairFreeCx X).ι P) (v : (pairFreeCx X).ι Q) :
    fourEvalF2 X p q α β k
        (tdR (pairFreeCx X) (pairFreeCx X) k P Q h
          (Finsupp.single u 1) (Finsupp.single v 1)) = 0 := by
  cases Q with
  | zero => rw [tdR_zero, map_zero]
  | succ Q' =>
      obtain ⟨⟨⟨a1, a2⟩, h1⟩, x1, x2⟩ := u
      obtain ⟨⟨⟨a3, a4⟩, h2⟩, x3, x4⟩ := v
      have hgen : tensorDGen (singFreeCx X) (singFreeCx X) Q'
            (⟨⟨(a3, a4), h2⟩, (x3, x4)⟩ :
              TensorIdx (singFreeCx X) (singFreeCx X) (Q' + 1))
          = tdL (singFreeCx X) (singFreeCx X) Q' a3 a4 h2
              (Finsupp.single x3 1) (Finsupp.single x4 1)
            + tdR (singFreeCx X) (singFreeCx X) Q' a3 a4 h2
              (Finsupp.single x3 1) (Finsupp.single x4 1) := rfl
      have hu : (Finsupp.single (⟨⟨(a1, a2), h1⟩, (x1, x2)⟩ :
              TensorIdx (singFreeCx X) (singFreeCx X) P) (1 : ZMod 2))
          = tenElt (singFreeCx X) (singFreeCx X) (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P)
              (Finsupp.single x1 1) (Finsupp.single x2 1) :=
        (tenElt_single_single (singFreeCx X) (singFreeCx X) _ x1 x2).symm
      have hA : fourEvalF2 X p q α β k
          (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P, Q'), by omega⟩ : Steenrod.PairDeg k)
            (tenElt (singFreeCx X) (singFreeCx X) (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P)
              (Finsupp.single x1 1) (Finsupp.single x2 1))
            (tdL (singFreeCx X) (singFreeCx X) Q' a3 a4 h2
              (Finsupp.single x3 1) (Finsupp.single x4 1))) = 0 := by
        cases a3 with
        | zero => rw [tdL_zero, tenElt_zero_right, map_zero]
        | succ a3' =>
            rw [tdL_succ]
            have hw : evLin X p α a3' ((singFreeCx X).d a3' (Finsupp.single x3 1)) = 0 := by
              rw [singFreeCx_d]
              exact evLin_bdU_of_cocycle X p α hα a3' (Finsupp.single x3 1)
            exact fourEvalF2_quadElt_of_three X p q α β k P Q' a1 a2 a3' a4 (by omega) h1
              (by omega) (Finsupp.single x1 1) (Finsupp.single x2 1)
              ((singFreeCx X).d a3' (Finsupp.single x3 1)) (Finsupp.single x4 1) hw
      have hB : fourEvalF2 X p q α β k
          (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P, Q'), by omega⟩ : Steenrod.PairDeg k)
            (tenElt (singFreeCx X) (singFreeCx X) (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P)
              (Finsupp.single x1 1) (Finsupp.single x2 1))
            (tdR (singFreeCx X) (singFreeCx X) Q' a3 a4 h2
              (Finsupp.single x3 1) (Finsupp.single x4 1))) = 0 := by
        cases a4 with
        | zero => rw [tdR_zero, tenElt_zero_right, map_zero]
        | succ a4' =>
            rw [tdR_succ]
            have hw : evLin X q β a4' ((singFreeCx X).d a4' (Finsupp.single x4 1)) = 0 := by
              rw [singFreeCx_d]
              exact evLin_bdU_of_cocycle X q β hβ a4' (Finsupp.single x4 1)
            exact fourEvalF2_quadElt_of_four X p q α β k P Q' a1 a2 a3 a4' (by omega) h1
              (by omega) (Finsupp.single x1 1) (Finsupp.single x2 1)
              (Finsupp.single x3 1) ((singFreeCx X).d a4' (Finsupp.single x4 1)) hw
      rw [tdR_succ, pairFreeCx_d, tensorD_single, one_smul, hgen, hu, tenElt_add_right,
        map_add, hA, hB, add_zero]

/-! ## 3. The functional annihilates boundaries -/

/-- **The evaluating functional kills boundaries.** -/
theorem fourEvalF2_tensorD (hα : cochainCoboundary (ZMod 2) X p α = 0)
    (hβ : cochainCoboundary (ZMod 2) X q β = 0) (k : ℕ)
    (y : TensorIdx (pairFreeCx X) (pairFreeCx X) (k + 1) →₀ ZMod 2) :
    fourEvalF2 X p q α β k (tensorD (pairFreeCx X) (pairFreeCx X) k y) = 0 := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  | single Z c =>
      obtain ⟨⟨⟨P, Q⟩, h⟩, u, v⟩ := Z
      rw [tensorD_single, map_smul]
      have hz : tensorDGen (pairFreeCx X) (pairFreeCx X) k
            (⟨⟨(P, Q), h⟩, (u, v)⟩ : TensorIdx (pairFreeCx X) (pairFreeCx X) (k + 1))
          = tdL (pairFreeCx X) (pairFreeCx X) k P Q h
              (Finsupp.single u 1) (Finsupp.single v 1)
            + tdR (pairFreeCx X) (pairFreeCx X) k P Q h
              (Finsupp.single u 1) (Finsupp.single v 1) := rfl
      rw [hz, map_add, fourEvalF2_tdL_outer hα hβ k P Q h u v,
        fourEvalF2_tdR_outer hα hβ k P Q h u v, add_zero, smul_zero]

end

end GroupApproximation.CharClass
