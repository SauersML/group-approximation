import GroupApproximation.CharClass.BundleStabilize

/-!
# Complex vector bundles in the projection model, XIII: the block inclusion

`BundleStabilize` proves the stabilised homotopy for an abstract pair of
isometries with orthogonal ranges.  This file names the concrete instance the
Euler class is stated over: the left block inclusion

    cpBlockIncl d : C(ℂP^d, ℂP^{2d+1})

induced by `ℂ^{d+1} ↪ ℂ^{d+1} ⊕ ℂ^{d+1} ≅ ℂ^{2d+2}`, together with the entry
description that lets a consumer compute with it -- which is what identifies the
image of the degree-two generator, hence the injectivity on `H²` that converts
the homotopy after stabilising into equality of Euler classes before.

The three entry lemmas determine the matrix completely, because
`blockEquiv d` is a bijection: an index is either `Sum.inl i` or `Sum.inr k`,
the first giving the entry of `z` and the second giving zero.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### Entries of the block isometry -/

section Entries

variable {ι κ ρ : Type} [Fintype ι] [Fintype κ] [DecidableEq ρ]

omit [Fintype ι] [Fintype κ] in
theorem sumInclLeft_apply (eqv : ι ⊕ κ ≃ ρ) (s : ρ) (i : ι) :
    sumInclLeft eqv s i = if s = eqv (Sum.inl i) then (1 : ℂ) else 0 := by
  rw [sumInclLeft, Matrix.submatrix_apply, Matrix.one_apply]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem sumInclLeft_apply_left [DecidableEq ι] (eqv : ι ⊕ κ ≃ ρ) (i m : ι) :
    sumInclLeft eqv (eqv (Sum.inl i)) m = if i = m then (1 : ℂ) else 0 := by
  rw [sumInclLeft_apply]
  by_cases h : i = m
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hc
    exact h (Sum.inl_injective (eqv.injective hc))

omit [Fintype ι] [Fintype κ] in
theorem sumInclLeft_apply_right (eqv : ι ⊕ κ ≃ ρ) (k : κ) (m : ι) :
    sumInclLeft eqv (eqv (Sum.inr k)) m = 0 := by
  rw [sumInclLeft_apply, if_neg]
  intro hc
  exact Sum.inr_ne_inl (eqv.injective hc)

omit [Fintype κ] in
/-- The conjugate has the entries of `z` on the left block. -/
theorem sumInclLeft_conj_apply [DecidableEq ι] (eqv : ι ⊕ κ ≃ ρ) (z : Matrix ι ι ℂ) (i j : ι) :
    (sumInclLeft eqv * z * (sumInclLeft eqv)ᴴ) (eqv (Sum.inl i)) (eqv (Sum.inl j)) = z i j := by
  have hrow : ∀ l : ι, (sumInclLeft eqv * z) (eqv (Sum.inl i)) l = z i l := by
    intro l
    rw [Matrix.mul_apply]
    simp [sumInclLeft_apply_left]
  rw [Matrix.mul_apply]
  have hterm : ∀ l : ι, (sumInclLeft eqv * z) (eqv (Sum.inl i)) l *
      ((sumInclLeft eqv)ᴴ) l (eqv (Sum.inl j)) = z i l * (if j = l then (1 : ℂ) else 0) := by
    intro l
    rw [hrow l, Matrix.conjTranspose_apply, sumInclLeft_apply_left]
    simp
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  simp

omit [Fintype κ] in
/-- The conjugate vanishes on a row outside the left block. -/
theorem sumInclLeft_conj_apply_row (eqv : ι ⊕ κ ≃ ρ) (z : Matrix ι ι ℂ) (k : κ) (t : ρ) :
    (sumInclLeft eqv * z * (sumInclLeft eqv)ᴴ) (eqv (Sum.inr k)) t = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hrow : (sumInclLeft eqv * z) (eqv (Sum.inr k)) l = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [sumInclLeft_apply_right, zero_mul]
  rw [hrow, zero_mul]

omit [Fintype κ] in
/-- The conjugate vanishes on a column outside the left block. -/
theorem sumInclLeft_conj_apply_col (eqv : ι ⊕ κ ≃ ρ) (z : Matrix ι ι ℂ) (s : ρ) (k : κ) :
    (sumInclLeft eqv * z * (sumInclLeft eqv)ᴴ) s (eqv (Sum.inr k)) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.conjTranspose_apply, sumInclLeft_apply_right, star_zero, mul_zero]

end Entries

/-! ### The block inclusion of complex projective spaces -/

section BlockIncl

/-- The splitting `ℂ^{d+1} ⊕ ℂ^{d+1} ≅ ℂ^{2d+2}`. -/
def blockEquiv (d : ℕ) : Fin (d + 1) ⊕ Fin (d + 1) ≃ Fin (2 * d + 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- **The left block inclusion `ℂP^d ↪ ℂP^{2d+1}`**, induced by the linear
isometric embedding `ℂ^{d+1} ↪ ℂ^{d+1} ⊕ ℂ^{d+1} ≅ ℂ^{2d+2}`. -/
noncomputable def cpBlockIncl (d : ℕ) : C(CP d, CP (2 * d + 1)) :=
  cpEmbed (sumInclLeft (blockEquiv d)) (sumInclLeft_isometry (blockEquiv d))

theorem cpBlockIncl_apply (d : ℕ) (z : CP d) :
    (cpBlockIncl d z : Matrix (Fin (2 * d + 1 + 1)) (Fin (2 * d + 1 + 1)) ℂ)
      = sumInclLeft (blockEquiv d) * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
        * (sumInclLeft (blockEquiv d))ᴴ := rfl

/-- **On the left block the entries are those of `z`.** -/
theorem cpBlockIncl_apply_left (d : ℕ) (z : CP d) (i j : Fin (d + 1)) :
    (cpBlockIncl d z : Matrix (Fin (2 * d + 1 + 1)) (Fin (2 * d + 1 + 1)) ℂ)
        (blockEquiv d (Sum.inl i)) (blockEquiv d (Sum.inl j))
      = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j := by
  rw [cpBlockIncl_apply]
  exact sumInclLeft_conj_apply (blockEquiv d) _ i j

/-- **Off the left block the entries vanish**, in the row index. -/
theorem cpBlockIncl_apply_row (d : ℕ) (z : CP d) (k : Fin (d + 1))
    (t : Fin (2 * d + 1 + 1)) :
    (cpBlockIncl d z : Matrix (Fin (2 * d + 1 + 1)) (Fin (2 * d + 1 + 1)) ℂ)
        (blockEquiv d (Sum.inr k)) t = 0 := by
  rw [cpBlockIncl_apply]
  exact sumInclLeft_conj_apply_row (blockEquiv d) _ k t

/-- **Off the left block the entries vanish**, in the column index. -/
theorem cpBlockIncl_apply_col (d : ℕ) (z : CP d) (s : Fin (2 * d + 1 + 1))
    (k : Fin (d + 1)) :
    (cpBlockIncl d z : Matrix (Fin (2 * d + 1 + 1)) (Fin (2 * d + 1 + 1)) ℂ)
        s (blockEquiv d (Sum.inr k)) = 0 := by
  rw [cpBlockIncl_apply]
  exact sumInclLeft_conj_apply_col (blockEquiv d) _ s k

/-- **Isomorphic line bundles have homotopic classifying maps after the block
inclusion.**  This is the hypothesis of the Euler class's invariance under
isomorphism: composing with an injection on `H²` turns it into equality of the
classes before stabilising. -/
theorem homotopic_classifyOne_blockIncl {X : Type} [TopologicalSpace X] {d : ℕ}
    {p q : Bundle X (Fin (d + 1))} (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1)
    (e : BundleIso p q) :
    ((cpBlockIncl d).comp (classifyOne p hp)).Homotopic
      ((cpBlockIncl d).comp (classifyOne q hq)) :=
  homotopic_cpEmbed_same e (sumInclLeft_isometry (blockEquiv d))
    (sumInclRight_isometry (blockEquiv d))
    (sumInclLeft_conjTranspose_mul_right (blockEquiv d))
    (sumInclRight_conjTranspose_mul_left (blockEquiv d)) hp hq

end BlockIncl

end Bundle

end CharClass
end GroupApproximation
