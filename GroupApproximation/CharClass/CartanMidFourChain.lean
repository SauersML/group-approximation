import GroupApproximation.CharClass.CartanMidFour

/-!
# The middle-four interchange is a chain map

`cc-steenrod`'s corrected second composite is the interchange applied to the
un-transposed grouping, so their Leibniz rule sits one interchange away from the
value they need, and crossing that step is exactly this theorem.

The mathematics is four terms.  The differential of a nested tensor is the sum of
the four per-slot boundaries, in characteristic two with no signs, and regrouping
does not touch the slots.  So both sides are the same four terms and the theorem
is a matching.

What makes it long is arithmetic, not algebra: a sum of two variables is not
syntactically a successor until the second is split, and the four degree sums
`a₁+a₂`, `a₃+a₄`, `a₁+a₃`, `a₂+a₄` all have to be in that form before the two
halves of the differential can be evaluated.  Splitting the four degrees puts all
four sums in normal form at once.

This file currently carries the two expansion lemmas the proof runs on.  The
identity itself is a matching of four terms, but putting the four degree sums
into successor form costs a sixteen-branch case split, and a uniform tactic over
those branches exceeds the elaboration budget: in any branch where the outer
half is not reached by `tdL_nested`, the fallback re-introduces the structure
projection of `tensorFreeCx`, whose `d_d` field is a large proof, and every later
match in that branch pays for it.  The remaining work is to replace the uniform
tactic by four named slot terms, each with a two-case proof, and two grouping
lemmas; that keeps every step small and the projection out of all of them.

## Main results

* `tensorFreeCx_d` — the differential of a tensor, without forcing the projection.
* `tdL_nested`, `tdR_nested` — the two halves of the differential of a nested
  tensor, on a decomposable inner factor, with the projection spent once.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-- The differential of a tensor product, stated so that nothing downstream has
to force the structure projection. -/
theorem tensorFreeCx_d (k : ℕ) : (tensorFreeCx A B).d k = tensorD A B k := rfl

/-- Expanding the left half of the differential of a nested tensor on a
decomposable inner factor. -/
theorem tdL_nested (k P' Q a1 a2 : ℕ) (h : P' + 1 + Q = k + 1) (h1 : a1 + a2 = P' + 1)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (V : (tensorFreeCx C D).ι Q →₀ ZMod 2) :
    tdL (tensorFreeCx A B) (tensorFreeCx C D) k (P' + 1) Q h
        (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg (P' + 1)) w1 w2) V
      = tenElt (tensorFreeCx A B) (tensorFreeCx C D)
            (⟨(P', Q), by omega⟩ : Steenrod.PairDeg k)
            (tdL A B P' a1 a2 h1 w1 w2) V
        + tenElt (tensorFreeCx A B) (tensorFreeCx C D)
            (⟨(P', Q), by omega⟩ : Steenrod.PairDeg k)
            (tdR A B P' a1 a2 h1 w1 w2) V := by
  rw [tdL_succ, tensorFreeCx_d, tensorD_tenElt, tenElt_add_left]

/-- Expanding the right half of the differential of a nested tensor on a
decomposable inner factor. -/
theorem tdR_nested (k P Q' a3 a4 : ℕ) (h : P + (Q' + 1) = k + 1) (h2 : a3 + a4 = Q' + 1)
    (U : (tensorFreeCx A B).ι P →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tdR (tensorFreeCx A B) (tensorFreeCx C D) k P (Q' + 1) h U
        (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg (Q' + 1)) w3 w4)
      = tenElt (tensorFreeCx A B) (tensorFreeCx C D)
            (⟨(P, Q'), by omega⟩ : Steenrod.PairDeg k) U
            (tdL C D Q' a3 a4 h2 w3 w4)
        + tenElt (tensorFreeCx A B) (tensorFreeCx C D)
            (⟨(P, Q'), by omega⟩ : Steenrod.PairDeg k) U
            (tdR C D Q' a3 a4 h2 w3 w4) := by
  rw [tdR_succ, tensorFreeCx_d, tensorD_tenElt, tenElt_add_right]

/-! ## The chain-map property -/

end

end GroupApproximation.CharClass
