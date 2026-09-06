import GroupApproximation.CharClass.CartanFreeCxSwap
import GroupApproximation.CharClass.CartanFreeCxHom

/-!
# The middle-four interchange, and why it turns `(12)(34)` into `(13)(24)`

The second composite of the internal Cartan comparison is
`τ₂₃ ∘ (Φ ⊗ Φ) ∘ (regrouping) ∘ (Δ_W ⊗ Φ₀)`, and the outer `τ₂₃` is not
decoration.  Without it the composite is equivariant for the permutation that
swaps inside each block, `(12)(34)`, while the first composite is equivariant for
the block swap `(13)(24)`.  Acyclic models compares two maps for the *same*
action, so one of them has to be conjugated into the other.

That is exactly what `τ₂₃` does, and the identity behind it is a two-line
computation in the symmetric group: with `σ = (12)(34)` and `τ = (23)`,

```text
τ σ = (1 3 4 2) = (13)(24) τ .
```

so `τ ∘ M` is `(13)(24)`-equivariant whenever `M` is `(12)(34)`-equivariant.

In the nested presentation of the fourfold this file's `midIdx` is `τ₂₃`, and the
conjugation identity `midIdx_tenSwapIdx` is **`rfl`**: regrouping and then
exchanging blocks is literally the same index as exchanging inside each block and
then regrouping.  Nothing has to be transported, because the degrees are carried
as data and the sum constraints are propositions.

## Main results

* `midIdx`, `midSwap` — the interchange on the index and on chains.
* `swapHom` — the factor swap of a tensor square, as a chain map.
* `midSwap_blockSwap` — **the conjugation**: regrouping carries the
  swap-inside-each-block action to the block swap.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (A B C D : FreeCx)

/-! ## 1. The interchange on the index -/

/-- **The middle-four interchange.**  `(x₁ ⊗ x₂) ⊗ (x₃ ⊗ x₄) ↦
(x₁ ⊗ x₃) ⊗ (x₂ ⊗ x₄)`, on the index of the nested tensor.  It is cast-free:
each of the four degrees is carried as data and each sum constraint is a
proposition. -/
def midIdx {k : ℕ} (q : TensorIdx (tensorFreeCx A B) (tensorFreeCx C D) k) :
    TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k :=
  ⟨⟨(q.2.1.1.val.1 + q.2.2.1.val.1, q.2.1.1.val.2 + q.2.2.1.val.2), by
      have h := q.1.property
      have h1 := q.2.1.1.property
      have h2 := q.2.2.1.property
      omega⟩,
    (⟨⟨(q.2.1.1.val.1, q.2.2.1.val.1), rfl⟩, (q.2.1.2.1, q.2.2.2.1)⟩,
     ⟨⟨(q.2.1.1.val.2, q.2.2.1.val.2), rfl⟩, (q.2.1.2.2, q.2.2.2.2)⟩)⟩

/-- The interchange on chains. -/
def midSwap (k : ℕ) :
    (TensorIdx (tensorFreeCx A B) (tensorFreeCx C D) k →₀ ZMod 2) →ₗ[ZMod 2]
      (TensorIdx (tensorFreeCx A C) (tensorFreeCx B D) k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (midIdx A B C D)

@[simp] theorem midSwap_single (k : ℕ)
    (q : TensorIdx (tensorFreeCx A B) (tensorFreeCx C D) k) (c : ZMod 2) :
    midSwap A B C D k (Finsupp.single q c)
      = Finsupp.single (midIdx A B C D q) c := by
  unfold midSwap
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ## 2. The factor swap, as a chain map -/

/-- The factor swap of a tensor square, as a chain map: it commutes with the
differential by `tensorD_tenSwap`. -/
noncomputable def swapHom (A : FreeCx) :
    FreeCxHom (tensorFreeCx A A) (tensorFreeCx A A) where
  f k := tenSwap A k
  comm k u := (tensorD_tenSwap A k u).symm

/-! ## 3. The conjugation -/

/-- **The interchange carries the swap-inside-each-block action to the block
swap.**  This is the identity `τ (12)(34) = (13)(24) τ` in the symmetric group,
and in the nested presentation it is `rfl` on the index. -/
theorem midIdx_tenSwapIdx (A : FreeCx) {k : ℕ}
    (q : TensorIdx (tensorFreeCx A A) (tensorFreeCx A A) k) :
    midIdx A A A A (⟨q.1, (tenSwapIdx A q.2.1, tenSwapIdx A q.2.2)⟩ :
        TensorIdx (tensorFreeCx A A) (tensorFreeCx A A) k)
      = tenSwapIdx (tensorFreeCx A A) (midIdx A A A A q) := rfl

/-- The same identity on chains: the interchange conjugates the action that
swaps inside each block into the action that exchanges the blocks. -/
theorem midSwap_blockSwap (A : FreeCx) (k : ℕ)
    (y : TensorIdx (tensorFreeCx A A) (tensorFreeCx A A) k →₀ ZMod 2) :
    midSwap A A A A k (tenHom (swapHom A) (swapHom A) k y)
      = tenSwap (tensorFreeCx A A) k (midSwap A A A A k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rfl
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single q c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, u, v⟩ := q
      have hs : (Finsupp.single (⟨⟨(a, b), hab⟩, (u, v)⟩ :
              TensorIdx (tensorFreeCx A A) (tensorFreeCx A A) k) c)
          = c • tenElt (tensorFreeCx A A) (tensorFreeCx A A)
              (⟨(a, b), hab⟩ : Steenrod.PairDeg k)
              (Finsupp.single u 1) (Finsupp.single v 1) := by
        rw [tenElt_single_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      have h1 : (swapHom A).f a (Finsupp.single u (1 : ZMod 2))
          = Finsupp.single (tenSwapIdx A u) 1 := tenSwap_single A a u 1
      have h2 : (swapHom A).f b (Finsupp.single v (1 : ZMod 2))
          = Finsupp.single (tenSwapIdx A v) 1 := tenSwap_single A b v 1
      rw [hs, map_smul, map_smul, map_smul, map_smul, tenHom_tenElt, h1, h2,
        tenElt_single_single, tenElt_single_single, midSwap_single, midSwap_single,
        tenSwap_single]
      rfl

/-! ## 4. The interchange on a fourfold decomposable -/

/-- The interchange on a fourfold basis element. -/
theorem midSwap_tenElt4_single (k P Q a1 a2 a3 a4 : ℕ)
    (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (h' : a1 + a3 + (a2 + a4) = k)
    (x1 : A.ι a1) (x2 : B.ι a2) (x3 : C.ι a3) (x4 : D.ι a4) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P)
            (Finsupp.single x1 1) (Finsupp.single x2 1))
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q)
            (Finsupp.single x3 1) (Finsupp.single x4 1)))
      = tenElt (tensorFreeCx A C) (tensorFreeCx B D)
          (⟨(a1 + a3, a2 + a4), h'⟩ : Steenrod.PairDeg k)
          (tenElt A C (⟨(a1, a3), rfl⟩ : Steenrod.PairDeg (a1 + a3))
            (Finsupp.single x1 1) (Finsupp.single x3 1))
          (tenElt B D (⟨(a2, a4), rfl⟩ : Steenrod.PairDeg (a2 + a4))
            (Finsupp.single x2 1) (Finsupp.single x4 1)) := by
  rw [tenElt_single_single, tenElt_single_single, tenElt_single_single, midSwap_single,
    tenElt_single_single, tenElt_single_single, tenElt_single_single]
  rfl

/-- **The interchange on a fourfold decomposable element.**  This is the form the
chain-map property is proved in: every element of the nested tensor is a sum of
these, with the four degrees fixed. -/
theorem midSwap_tenElt4 (k P Q a1 a2 a3 a4 : ℕ)
    (h : P + Q = k) (h1 : a1 + a2 = P) (h2 : a3 + a4 = Q)
    (h' : a1 + a3 + (a2 + a4) = k)
    (w1 : A.ι a1 →₀ ZMod 2) (w2 : B.ι a2 →₀ ZMod 2)
    (w3 : C.ι a3 →₀ ZMod 2) (w4 : D.ι a4 →₀ ZMod 2) :
    midSwap A B C D k
        (tenElt (tensorFreeCx A B) (tensorFreeCx C D) (⟨(P, Q), h⟩ : Steenrod.PairDeg k)
          (tenElt A B (⟨(a1, a2), h1⟩ : Steenrod.PairDeg P) w1 w2)
          (tenElt C D (⟨(a3, a4), h2⟩ : Steenrod.PairDeg Q) w3 w4))
      = tenElt (tensorFreeCx A C) (tensorFreeCx B D)
          (⟨(a1 + a3, a2 + a4), h'⟩ : Steenrod.PairDeg k)
          (tenElt A C (⟨(a1, a3), rfl⟩ : Steenrod.PairDeg (a1 + a3)) w1 w3)
          (tenElt B D (⟨(a2, a4), rfl⟩ : Steenrod.PairDeg (a2 + a4)) w2 w4) := by
  induction w1 using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [tenElt_add_left, tenElt_add_left, map_add, hf, hg,
        tenElt_add_left, tenElt_add_left]
  | single x1 c1 =>
      rcases zmod2_eq_zero_or_one c1 with rfl | rfl
      · rw [Finsupp.single_zero]
        simp
      · induction w2 using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg =>
            rw [tenElt_add_right, tenElt_add_left, map_add, hf, hg,
              tenElt_add_left, tenElt_add_right]
        | single x2 c2 =>
            rcases zmod2_eq_zero_or_one c2 with rfl | rfl
            · rw [Finsupp.single_zero]
              simp
            · induction w3 using Finsupp.induction_linear with
              | zero => simp
              | add f g hf hg =>
                  rw [tenElt_add_left, tenElt_add_right, map_add, hf, hg,
                    tenElt_add_right, tenElt_add_left]
              | single x3 c3 =>
                  rcases zmod2_eq_zero_or_one c3 with rfl | rfl
                  · rw [Finsupp.single_zero]
                    simp
                  · induction w4 using Finsupp.induction_linear with
                    | zero => simp
                    | add f g hf hg =>
                        rw [tenElt_add_right, tenElt_add_right, map_add, hf, hg,
                          tenElt_add_right, tenElt_add_right]
                    | single x4 c4 =>
                        rcases zmod2_eq_zero_or_one c4 with rfl | rfl
                        · rw [Finsupp.single_zero]
                          simp
                        · exact midSwap_tenElt4_single A B C D k P Q a1 a2 a3 a4
                            h h1 h2 h' x1 x2 x3 x4

end

end GroupApproximation.CharClass
