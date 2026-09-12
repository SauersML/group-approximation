import GroupApproximation.CharClass.ParityEven
import GroupApproximation.CharClass.LIXSectionManuscript

/-!
# Step D, instantiated at the LIX base

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step D).

`CharClass/ParityEven.lean` (lane `cc-wu`, green) proves the even side over an abstract
`ParityData R H`: for `m` even, the top mod-2 Chern class `γ_{m+3}` of any bundle whose
Künneth data satisfies the listed identities vanishes.  This file records the shape that
data takes at the concrete base

```text
N = S¹ × S⁵ × Y ,   Y = ∏ⱼ ℂP^{dⱼ} ,   R = H^*(Y; F₂) ,   H = H^*(N; F₂),
```

and reduces Step D for the LIX bundle to it in one line.  The Künneth splitting, the
Steenrod squares and the mod-2 Chern classes are owed by `cc-cohom-api`, `cc-steenrod`
and `cc-projective`; until they land, `LIXParityInput` is the single named hypothesis that
carries them, and it is a `structure` field, never a `sorry`.

## The degree bookkeeping, checked

`t` has degree `1` (the circle) and `x` degree `5` (the five-sphere), so `t x` has degree
`6` and the Künneth component `b k` of `γ k` has degree `2k - 6`.  cc-wu's field `sq_b`,
which reads `2 * k < j + 6 → SqR j (b k) = 0`, is then exactly instability, confirming
those two degrees.  On the other side `trace_Vmat` below gives `rank V = (∑ⱼ dⱼ) + 3`,
which is cc-wu's index `(∑ⱼ dⱼ) + 3`, and `trace_mappingTorus` transports it to `W_g`.
Finally `dim N = 1 + 5 + 2 ∑ⱼ dⱼ = 2 rank V`, so the class sits in the top degree.

## Main results

* `trace_Hmat`, `trace_Vmat` — `rank H = ∑ⱼ dⱼ` and `rank V = (∑ⱼ dⱼ) + 3`.
* `LIXParityInput` — the concrete Step D data.
* `LIXParityInput.gamma_top_eq_zero` — **Step D**: `γ_{(∑ⱼ dⱼ)+3}(W_g) = 0` whenever every
  `dⱼ` is even.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The rank of `V`, explicitly -/

variable {dd : Fin ℓ → ℕ}

theorem trace_Hmat (m : baseM dd) : Matrix.trace (Hmat m) = ((∑ j, dd j : ℕ) : ℂ) := by
  rw [Hmat, Matrix.trace_blockDiagonal']
  have hone : ∀ b : HBlk dd,
      Matrix.trace ((m.2 b.1 : CP (dd b.1)) :
        Matrix (Fin (dd b.1 + 1)) (Fin (dd b.1 + 1)) ℂ) = 1 := fun b => trace_coe (m.2 b.1)
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hone b]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.card_univ, Fintype.card_sigma]
  simp

/-- The trace of a `2 × 2` block matrix with **different** index types on the two
diagonal blocks.  `MappingTorusProjection.trace_fromBlocks'` is the square-blocks version;
`V = 𝟏³ ⊕ H` needs this one. -/
theorem trace_fromBlocks_gen {l m : Type*} [Fintype l] [Fintype m] (A : Matrix l l ℂ)
    (B : Matrix l m ℂ) (C : Matrix m l ℂ) (D : Matrix m m ℂ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem trace_Vmat (m : baseM dd) :
    Matrix.trace (Vmat m) = (((∑ j, dd j : ℕ) + 3 : ℕ) : ℂ) := by
  rw [Vmat, trace_fromBlocks_gen, trace_Hmat, Matrix.trace_one, Fintype.card_fin]
  push_cast
  ring

/-! ## 2. The concrete Step D data -/

/-- **The Künneth, Steenrod and Chern data of Step D at the LIX base.**

`R` is `H^*(Y; F₂)` and `H` is `H^*(S¹ × S⁵ × Y; F₂)`; `data` is `cc-wu`'s abstract
package, `gen j` is the degree-two generator `e(Lⱼ)`, and `slice` says the restriction of
the total mod-2 Chern class to the slice is `∏ⱼ (1 + hⱼ)^{dⱼ}`.

The slice hypothesis is exactly what `mappingTorus_north` makes cheap: the mapping torus
restricted to the north-pole slice is `V ⊕ 0` **on the nose**, and a zero block contributes
nothing to a total Chern class, so no Murray--von Neumann transport sits between `γ(W_g)`
restricted to the slice and `γ(V)`. -/
structure LIXParityInput (R H : Type*) [CommRing R] [CommRing H] (dd : Fin ℓ → ℕ) where
  /-- `cc-wu`'s abstract even-side package. -/
  data : ParityData R H
  /-- The degree-two generators `hⱼ = e(Lⱼ)` of `H^*(Y; F₂)`. -/
  gen : Fin ℓ → R
  /-- The slice class of `W_g` is `∏ⱼ (1 + hⱼ)^{dⱼ}`. -/
  slice : ∀ q : ℕ, data.a q = (sliceClass Finset.univ gen dd).coeff q

/-- **Step D at the LIX base.**  Every `dⱼ` even forces the top mod-2 Chern class of the
mapping torus to vanish.  Only evenness is used, not the tower's powers of two. -/
theorem LIXParityInput.gamma_top_eq_zero {R H : Type*} [CommRing R] [CommRing H]
    (P : LIXParityInput R H dd) (hd : ∀ j, Even (dd j)) :
    P.data.γ ((∑ j, dd j) + 3) = 0 :=
  P.data.gamma_top_eq_zero_of_slice Finset.univ P.gen dd (fun j _ => hd j) P.slice

end GroupApproximation.CharClass
