import GroupApproximation.CharClass.CartanMidFourSrc

/-!
# The middle-four interchange is a chain map

The two sides of the chain-map identity are the sum of the same four slot terms,
so on a fourfold decomposable they agree; and every basis element of the fourfold
complex *is* a fourfold decomposable of singles, so they agree everywhere.

This is what composite B needs.  The block swap of a tensor square, with the pair
complex as the factor, is the permutation `(13)(24)`, and that is exactly this
interchange; the transposition that conjugates one equivariance into the other
lives at the index level, where `midIdx_tenSwapIdx` already records it.

## Main results

* `tensorD_midSwap_tenElt` — the identity on a fourfold decomposable.
* `single_tenElt4` — every basis element is such a decomposable.
* `tensorD_midSwap` — the identity on every chain.
* `midSwapHom` — the interchange packaged as a `FreeCxHom`.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-- **The chain-map identity on a fourfold decomposable.**  Both sides are the
sum of the same four slot terms. -/
theorem tensorD_midSwap_tenElt (k P Q a1 a2 a3 a4 : ℕ)
    (h : P + Q = k + 1) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    tensorD (tensorFreeCx A C) (tensorFreeCx B D) k
        (midSwap A B C D (k + 1)
          (tenElt (tensorFreeCx A B) (tensorFreeCx C D)
            (⟨(P, Q), h⟩ : Steenrod.PairDeg (k + 1))
            (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
            (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4)))
      = midSwap A B C D k
          (tensorD (tensorFreeCx A B) (tensorFreeCx C D) k
            (tenElt (tensorFreeCx A B) (tensorFreeCx C D)
              (⟨(P, Q), h⟩ : Steenrod.PairDeg (k + 1))
              (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
              (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))) := by
  rw [midSwap_tenElt4'' A B C D (k + 1) P Q (a1 + a3) (a2 + a4) a1 a2 a3 a4 h h1 h2
      rfl rfl (by omega),
    tensorD_tenElt_grouped A B C D k (a1 + a3) (a2 + a4) (a1 + a3 - 1) (a2 + a4 - 1)
      a1 a2 a3 a4 (by omega) rfl rfl rfl rfl w1 w2 w3 w4,
    midSwap_tensorD_grouped A B C D k P Q (a1 + a3) (a2 + a4) (a1 + a3 - 1) (a2 + a4 - 1)
      a1 a2 a3 a4 h h1 h2 rfl rfl rfl rfl w1 w2 w3 w4]

/-- Every basis element of the fourfold complex is a fourfold decomposable of
singles. -/
theorem single_tenElt4 (k P Q a1 a2 a3 a4 : ℕ)
    (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (x1 : A.ι a1) (x2 : B.ι a2) (x3 : C.ι a3) (x4 : D.ι a4) :
    tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
        (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P)
          (Finsupp.single x1 1) (Finsupp.single x2 1))
        (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q)
          (Finsupp.single x3 1) (Finsupp.single x4 1))
      = Finsupp.single
          (⟨⟨(P, Q), h⟩, (⟨⟨(a1, a2), h1⟩, (x1, x2)⟩, ⟨⟨(a3, a4), h2⟩, (x3, x4)⟩)⟩ :
            TensorIdx (tensorFreeCx A B) (tensorFreeCx C D) k) (1 : ZMod 2) := by
  rw [tenElt_single_single, tenElt_single_single, tenElt_single_single]

/-- **The middle-four interchange is a chain map.** -/
theorem tensorD_midSwap (k : ℕ)
    (z : TensorIdx (tensorFreeCx A B) (tensorFreeCx C D) (k + 1) →₀ ZMod 2) :
    tensorD (tensorFreeCx A C) (tensorFreeCx B D) k (midSwap A B C D (k + 1) z)
      = midSwap A B C D k (tensorD (tensorFreeCx A B) (tensorFreeCx C D) k z) := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single q c =>
      obtain ⟨⟨⟨P, Q⟩, hPQ⟩, ⟨⟨⟨a1, a2⟩, h1⟩, x1, x2⟩, ⟨⟨⟨a3, a4⟩, h2⟩, x3, x4⟩⟩ := q
      rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul,
        ← single_tenElt4 A B C D (k + 1) P Q a1 a2 a3 a4 hPQ h1 h2 x1 x2 x3 x4,
        tensorD_midSwap_tenElt A B C D k P Q a1 a2 a3 a4 hPQ h1 h2
          (Finsupp.single x1 1) (Finsupp.single x2 1) (Finsupp.single x3 1)
          (Finsupp.single x4 1)]

/-- The middle-four interchange as a map of complexes. -/
noncomputable def midSwapHom :
    FreeCxHom (tensorFreeCx (tensorFreeCx A B) (tensorFreeCx C D))
      (tensorFreeCx (tensorFreeCx A C) (tensorFreeCx B D)) where
  f k := midSwap A B C D k
  comm k u := (tensorD_midSwap A B C D k u).symm

theorem midSwapHom_f (k : ℕ) : (midSwapHom A B C D).f k = midSwap A B C D k := rfl

end

end GroupApproximation.CharClass
