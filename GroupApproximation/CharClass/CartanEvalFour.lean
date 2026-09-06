import GroupApproximation.CharClass.CartanEvalCocycle
import GroupApproximation.CharClass.CartanComparison

/-!
# The evaluating functional factors over the four slots

The functional of `CartanEvalFunctional.lean` is a product of four cochain
values, so on a fourfold decomposable it is the product of the four one-slot
pairings.  That is this file, and it is what turns the one-slot cocycle lemma of
`CartanEvalCocycle.lean` into the fourfold statement the comparison needs.

The proof is the fourfold induction, kept short the same way as in
`CartanMidFour.lean`: rather than pulling four scalars through the whole
expression, each coefficient is split into zero or one, because those are the
only elements of the field.

The four chains are typed through `(singFreeCx X).ι` rather than through
`singularSimplices` on purpose.  The slot of a `tenElt` is reached by a
projection on an explicit constructor, which reduces below the transparency that
lemma matching uses, whereas identifying `singularSimplices X a` with the slot
needs `singFreeCx` unfolded and it is a plain `def`.  Typed this way every lemma
about `tenElt` matches; typed the other way none of them does.

## Main results

* `fourEvalF2_tenElt4` — **the functional factors**: on a fourfold decomposable
  it is the product of the four one-slot pairings.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (X : TopCat.{0}) (p q : ℕ)
variable (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)

/-- The functional on a fourfold basis element, written as a product. -/
theorem fourEvalF2_tenElt4_single (k P Q a1 a2 a3 a4 : ℕ)
    (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (x1 : (singFreeCx X).ι a1) (x2 : (singFreeCx X).ι a2)
    (x3 : (singFreeCx X).ι a3) (x4 : (singFreeCx X).ι a4) :
    fourEvalF2 X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P)
            (Finsupp.single x1 1) (Finsupp.single x2 1))
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q)
            (Finsupp.single x3 1) (Finsupp.single x4 1)))
      = evAt X p α a1 x1 * evAt X q β a2 x2 * (evAt X p α a3 x3 * evAt X q β a4 x4) := by
  rw [tenElt_single_single, tenElt_single_single, tenElt_single_single,
    fourEvalF2_single, one_mul]
  rfl

/-- **The functional factors over the four slots.** -/
theorem fourEvalF2_tenElt4 (k P Q a1 a2 a3 a4 : ℕ)
    (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (w1 : (singFreeCx X).ι a1 →₀ ZMod 2) (w2 : (singFreeCx X).ι a2 →₀ ZMod 2)
    (w3 : (singFreeCx X).ι a3 →₀ ZMod 2) (w4 : (singFreeCx X).ι a4 →₀ ZMod 2) :
    fourEvalF2 X p q α β k
        (tenElt (pairFreeCx X) (pairFreeCx X) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tenElt (singFreeCx X) (singFreeCx X) (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = evLin X p α a1 w1 * evLin X q β a2 w2 * (evLin X p α a3 w3 * evLin X q β a4 w4) := by
  induction w1 using Finsupp.induction_linear with
  | zero =>
      have e0 : (evLin X p α a1) (0 : (singFreeCx X).ι a1 →₀ ZMod 2) = 0 := map_zero _
      rw [tenElt_zero_left, tenElt_zero_left, map_zero, e0, zero_mul, zero_mul]
  | add f g hf hg =>
      have e : (evLin X p α a1) (f + g) = (evLin X p α a1) f + (evLin X p α a1) g := map_add _ f g
      rw [tenElt_add_left, tenElt_add_left, map_add, hf, hg, e]
      ring
  | single x1 c1 =>
      rcases zmod2_eq_zero_or_one c1 with rfl | rfl
      · have e0 : (evLin X p α a1) (0 : (singFreeCx X).ι a1 →₀ ZMod 2) = 0 := map_zero _
        rw [Finsupp.single_zero, tenElt_zero_left, tenElt_zero_left, map_zero,
          e0, zero_mul, zero_mul]
      · induction w2 using Finsupp.induction_linear with
        | zero =>
            have e0 : (evLin X q β a2) (0 : (singFreeCx X).ι a2 →₀ ZMod 2) = 0 := map_zero _
            rw [tenElt_zero_right, tenElt_zero_left, map_zero, e0, mul_zero, zero_mul]
        | add f g hf hg =>
            have e : (evLin X q β a2) (f + g) = (evLin X q β a2) f + (evLin X q β a2) g := map_add _ f g
            rw [tenElt_add_right, tenElt_add_left, map_add, hf, hg, e]
            ring
        | single x2 c2 =>
            rcases zmod2_eq_zero_or_one c2 with rfl | rfl
            · have e0 : (evLin X q β a2) (0 : (singFreeCx X).ι a2 →₀ ZMod 2) = 0 :=
                map_zero _
              rw [Finsupp.single_zero, tenElt_zero_right, tenElt_zero_left, map_zero,
                e0, mul_zero, zero_mul]
            · induction w3 using Finsupp.induction_linear with
              | zero =>
                  have e0 : (evLin X p α a3) (0 : (singFreeCx X).ι a3 →₀ ZMod 2) = 0 :=
                    map_zero _
                  rw [tenElt_zero_left, tenElt_zero_right, map_zero, e0,
                    zero_mul, mul_zero]
              | add f g hf hg =>
                  have e : (evLin X p α a3) (f + g) = (evLin X p α a3) f + (evLin X p α a3) g := map_add _ f g
                  rw [tenElt_add_left, tenElt_add_right, map_add, hf, hg, e]
                  ring
              | single x3 c3 =>
                  rcases zmod2_eq_zero_or_one c3 with rfl | rfl
                  · have e0 : (evLin X p α a3) (0 : (singFreeCx X).ι a3 →₀ ZMod 2) = 0 :=
                      map_zero _
                    rw [Finsupp.single_zero, tenElt_zero_left, tenElt_zero_right,
                      map_zero, e0, zero_mul, mul_zero]
                  · induction w4 using Finsupp.induction_linear with
                    | zero =>
                        have e0 : (evLin X q β a4) (0 : (singFreeCx X).ι a4 →₀ ZMod 2) = 0 :=
                          map_zero _
                        rw [tenElt_zero_right, tenElt_zero_right, map_zero, e0,
                          mul_zero, mul_zero]
                    | add f g hf hg =>
                        have e : (evLin X q β a4) (f + g) = (evLin X q β a4) f + (evLin X q β a4) g := map_add _ f g
                        rw [tenElt_add_right, tenElt_add_right, map_add, hf, hg, e]
                        ring
                    | single x4 c4 =>
                        rcases zmod2_eq_zero_or_one c4 with rfl | rfl
                        · have e0 : (evLin X q β a4) (0 : (singFreeCx X).ι a4 →₀ ZMod 2) = 0 :=
                            map_zero _
                          rw [Finsupp.single_zero, tenElt_zero_right, tenElt_zero_right,
                            map_zero, e0, mul_zero, mul_zero]
                        · have s1 : (evLin X p α a1) (Finsupp.single x1 (1 : ZMod 2))
                              = evAt X p α a1 x1 :=
                            (evLin_single X p α a1 x1 1).trans (one_mul _)
                          have s2 : (evLin X q β a2) (Finsupp.single x2 (1 : ZMod 2))
                              = evAt X q β a2 x2 :=
                            (evLin_single X q β a2 x2 1).trans (one_mul _)
                          have s3 : (evLin X p α a3) (Finsupp.single x3 (1 : ZMod 2))
                              = evAt X p α a3 x3 :=
                            (evLin_single X p α a3 x3 1).trans (one_mul _)
                          have s4 : (evLin X q β a4) (Finsupp.single x4 (1 : ZMod 2))
                              = evAt X q β a4 x4 :=
                            (evLin_single X q β a4 x4 1).trans (one_mul _)
                          rw [fourEvalF2_tenElt4_single]
                          exact congr_arg₂ (· * ·) (congr_arg₂ (· * ·) s1.symm s2.symm)
                            (congr_arg₂ (· * ·) s3.symm s4.symm)

end

end GroupApproximation.CharClass
