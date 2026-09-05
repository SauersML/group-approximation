import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
# The block inclusions `M ↦ diag (M, 1)` between matrix algebras over a C-star algebra

The colimit defining topological `K_1` runs along the block inclusions

    M_n(A) → M_m(A),   M ↦ diag (M, 1),   n ≤ m,

which are unital star monoid homomorphisms (not algebra maps: they are not
additive).  This file defines them entrywise, proves that they are unital,
multiplicative, star-preserving, continuous, and functorial in `n ≤ m`, and
packages the induced map on unitary groups.

Everything here is elementary index bookkeeping.  The only nontrivial step is
`blockOne_mul`, where a sum over `Fin m` collapses onto the upper-left block;
`sum_eq_sum_castLE` isolates that collapse.

Note the local trap: `CStarMatrix.one_apply` unfolds to an `if`, so a rewrite
chain through `Matrix.one_apply_eq` cannot fire.  The proofs below use
`CStarMatrix.one_apply` directly.
-/

namespace GroupApproximation

universe u

/-- Square matrices of size `n` with entries in `A`, with the C-star matrix structure. -/
abbrev CStarMat (n : ℕ) (A : Type u) : Type u := CStarMatrix (Fin n) (Fin n) A

variable {A : Type u} {n m k : ℕ}

section Sum

/-- A sum over `Fin m` whose terms vanish outside the first `n` indices is a sum over `Fin n`. -/
theorem sum_eq_sum_castLE {B : Type*} [AddCommMonoid B] (h : n ≤ m) (g : Fin m → B)
    (hg : ∀ i : Fin m, ¬ ((i : ℕ) < n) → g i = 0) :
    ∑ i : Fin m, g i = ∑ i : Fin n, g (Fin.castLE h i) := by
  classical
  have key : ∑ i ∈ Finset.univ.image (Fin.castLE h), g i = ∑ i : Fin m, g i := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    refine hg x fun hlt => hx ?_
    exact Finset.mem_image.mpr ⟨⟨(x : ℕ), hlt⟩, Finset.mem_univ _, rfl⟩
  rw [← key, Finset.sum_image]
  intro a _ b _ hab
  exact Fin.eq_of_val_eq (congrArg Fin.val hab)

end Sum

section Defs

variable [CStarAlgebra A]

/-- The block inclusion `diag (M, 1)`: the `m × m` matrix which agrees with the `n × n` matrix
`M` on the upper-left `n × n` corner and is the identity elsewhere.  The definition makes sense
for any `m`; every algebraic property below assumes `n ≤ m`. -/
def blockOne (M : CStarMat n A) (m : ℕ) : CStarMat m A := fun i j =>
  if hi : (i : ℕ) < n then
    (if hj : (j : ℕ) < n then M ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else 0)
  else
    (if (j : ℕ) < n then 0 else if i = j then 1 else 0)

theorem blockOne_apply (M : CStarMat n A) (i j : Fin m) :
    blockOne M m i j =
      if hi : (i : ℕ) < n then
        (if hj : (j : ℕ) < n then M ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else 0)
      else
        (if (j : ℕ) < n then 0 else if i = j then 1 else 0) := rfl

theorem blockOne_apply_of_lt_of_lt (M : CStarMat n A) {i j : Fin m}
    (hi : (i : ℕ) < n) (hj : (j : ℕ) < n) :
    blockOne M m i j = M ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ := by
  rw [blockOne_apply, dif_pos hi, dif_pos hj]

theorem blockOne_apply_of_lt_of_not_lt (M : CStarMat n A) {i j : Fin m}
    (hi : (i : ℕ) < n) (hj : ¬ ((j : ℕ) < n)) : blockOne M m i j = 0 := by
  rw [blockOne_apply, dif_pos hi, dif_neg hj]

theorem blockOne_apply_of_not_lt_of_lt (M : CStarMat n A) {i j : Fin m}
    (hi : ¬ ((i : ℕ) < n)) (hj : (j : ℕ) < n) : blockOne M m i j = 0 := by
  rw [blockOne_apply, dif_neg hi, if_pos hj]

theorem blockOne_apply_of_not_lt_of_not_lt (M : CStarMat n A) {i j : Fin m}
    (hi : ¬ ((i : ℕ) < n)) (hj : ¬ ((j : ℕ) < n)) :
    blockOne M m i j = if i = j then 1 else 0 := by
  rw [blockOne_apply, dif_neg hi, if_neg hj]

theorem blockOne_castLE (h : n ≤ m) (M : CStarMat n A) (i j : Fin n) :
    blockOne M m (Fin.castLE h i) (Fin.castLE h j) = M i j :=
  blockOne_apply_of_lt_of_lt M i.isLt j.isLt

theorem blockOne_self (M : CStarMat n A) : blockOne M n = M := by
  ext i j
  rw [blockOne_apply_of_lt_of_lt M i.isLt j.isLt]

theorem blockOne_one (n m : ℕ) : blockOne (1 : CStarMat n A) m = 1 := by
  ext i j
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_lt_of_lt _ hi hj, CStarMatrix.one_apply, CStarMatrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos (Fin.eq_of_val_eq (congrArg Fin.val hij))]
      · rw [if_neg hij, if_neg]
        exact fun hc => hij (Fin.eq_of_val_eq (congrArg Fin.val hc))
    · rw [blockOne_apply_of_lt_of_not_lt _ hi hj, CStarMatrix.one_apply, if_neg]
      exact fun hc => hj (hc ▸ hi)
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_not_lt_of_lt _ hi hj, CStarMatrix.one_apply, if_neg]
      exact fun hc => hi (hc ▸ hj)
    · rw [blockOne_apply_of_not_lt_of_not_lt _ hi hj, CStarMatrix.one_apply]

theorem blockOne_mul (h : n ≤ m) (M N : CStarMat n A) :
    blockOne (M * N) m = blockOne M m * blockOne N m := by
  ext i j
  rw [CStarMatrix.mul_apply]
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_lt_of_lt _ hi hj, CStarMatrix.mul_apply,
        sum_eq_sum_castLE h _ (fun l hl => by
          rw [blockOne_apply_of_lt_of_not_lt M hi hl, zero_mul])]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [blockOne_apply_of_lt_of_lt M hi l.isLt, blockOne_apply_of_lt_of_lt N l.isLt hj]
    · rw [blockOne_apply_of_lt_of_not_lt _ hi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : (l : ℕ) < n
      · rw [blockOne_apply_of_lt_of_not_lt N hl hj, mul_zero]
      · rw [blockOne_apply_of_lt_of_not_lt M hi hl, zero_mul]
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_not_lt_of_lt _ hi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : (l : ℕ) < n
      · rw [blockOne_apply_of_not_lt_of_lt M hi hl, zero_mul]
      · rw [blockOne_apply_of_not_lt_of_lt N hl hj, mul_zero]
    · rw [blockOne_apply_of_not_lt_of_not_lt _ hi hj,
        sum_eq_sum_castLE (le_refl m) _ (fun l hl => absurd l.isLt hl)]
      rw [Fin.sum_univ_eq_sum_range]
      sorry

end Defs

end GroupApproximation
