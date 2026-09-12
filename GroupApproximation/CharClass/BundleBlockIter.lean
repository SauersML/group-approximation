import GroupApproximation.CharClass.BundleCoordEmbed
import GroupApproximation.CharClass.ProjectiveSpaceIterate

/-!
# Complex vector bundles in the projection model, XVIII: the block inclusion is
the iterated hyperplane inclusion

`cc-projective` computes the degree-two generator along the `k`-fold hyperplane
inclusion `cpInclIter`, and needs that computation transported to the block
inclusion, which is what an Euler class is defined against.  The transport is
`homotopic_cpEmbed_of_orthogonal`, and the only obstacle is arithmetic: the
`(d+1)`-fold iterate lands in `Fin (d + (d + 1) + 1)` while `cpBlockIncl` lands
in `Fin (2 * d + 1 + 1)`.  Those are equal but **not** definitionally, since
`2 * d` does not reduce for a variable `d`.

So this file states the block inclusion at the iterate's index rather than
casting between the two.  `blockEquivIter` is `blockEquiv` with its `finCongr`
aimed at `d + (d + 1) + 1`, everything downstream is the existing suite applied
to it, and no cast appears anywhere.  `cpBlockIncl` at `2 * d + 1` is untouched
(fleet rule 11).

## Main declarations

* `iterMat` — the matrix of the `k`-fold hyperplane inclusion, `shiftMat` folded.
* `iterMat_eq_coordIncl` — it is the coordinate inclusion of `i ↦ i + k`.
* `blockEquivIter`, `cpBlockInclIter` — the block inclusion at the iterate's index.
* `homotopic_cpBlockInclIter` — **the bridge**: the two are homotopic.
* `homotopic_classifyOne_blockInclIter` — Euler-class invariance at that index.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Iter

/-! ### The matrix of the iterated hyperplane inclusion -/

/-- The index map of the `k`-fold hyperplane inclusion, `i ↦ i + k`. -/
def iterFin (d : ℕ) : (k : ℕ) → Fin (d + 1) → Fin (d + k + 1)
  | 0 => id
  | (k + 1) => fun i => Fin.succ (iterFin d k i)

theorem iterFin_val (d k : ℕ) (i : Fin (d + 1)) : (iterFin d k i).val = i.val + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (iterFin d k i).val + 1 = i.val + (k + 1)
      rw [ih]
      omega

/-- The matrix of the `k`-fold hyperplane inclusion. -/
noncomputable def iterMat (d : ℕ) : (k : ℕ) → Matrix (Fin (d + k + 1)) (Fin (d + 1)) ℂ
  | 0 => 1
  | (k + 1) => shiftMat (d + k) * iterMat d k

theorem iterMat_zero (d : ℕ) : iterMat d 0 = 1 := rfl

theorem iterMat_succ (d k : ℕ) :
    iterMat d (k + 1) = shiftMat (d + k) * iterMat d k := rfl

theorem iterMat_isometry (d k : ℕ) : (iterMat d k)ᴴ * iterMat d k = 1 := by
  induction k with
  | zero =>
      rw [iterMat_zero, Matrix.conjTranspose_one, Matrix.one_mul]
  | succ k ih =>
      rw [iterMat_succ]
      exact isometry_mul ih (shiftMat_isometry (d + k))

/-- **The iterate's matrix is a coordinate inclusion**, of the index map `i ↦ i + k`. -/
theorem iterMat_eq_coordIncl (d k : ℕ) : iterMat d k = coordIncl (iterFin d k) := by
  induction k with
  | zero =>
      rw [iterMat_zero]
      ext s i
      rw [Matrix.one_apply, coordIncl_apply]
      rfl
  | succ k ih =>
      rw [iterMat_succ, ih, shiftMat_def]
      exact coordIncl_mul_coordIncl _ _

/-- The iterate factors one step at a time, as a composite of `cpEmbed`s. -/
theorem cpEmbed_iterMat_succ (d k : ℕ) :
    cpEmbed (iterMat d (k + 1)) (iterMat_isometry d (k + 1))
      = (cpEmbed (shiftMat (d + k)) (shiftMat_isometry (d + k))).comp
          (cpEmbed (iterMat d k) (iterMat_isometry d k)) :=
  (cpEmbed_comp (iterMat_isometry d k) (shiftMat_isometry (d + k))).symm

/-! ### The block inclusion at the iterate's index -/

/-- `blockEquiv` with its congruence aimed at the index the iterate lands in. -/
def blockEquivIter (d : ℕ) : Fin (d + 1) ⊕ Fin (d + 1) ≃ Fin (d + (d + 1) + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

theorem blockEquivIter_val_inl (d : ℕ) (i : Fin (d + 1)) :
    (blockEquivIter d (Sum.inl i)).val = i.val := by
  show (finCongr (by omega : (d + 1) + (d + 1) = d + (d + 1) + 1)
    (finSumFinEquiv (Sum.inl i))).val = i.val
  simp

/-- **The left block and the `(d+1)`-fold iterate have disjoint index ranges.**
The block sits in the first `d + 1` coordinates and the iterate shifts past
them. -/
theorem blockEquivIter_ne_iterFin (d : ℕ) (i k : Fin (d + 1)) :
    blockEquivIter d (Sum.inl i) ≠ iterFin d (d + 1) k := by
  intro h
  have hval : (blockEquivIter d (Sum.inl i)).val = (iterFin d (d + 1) k).val := by rw [h]
  rw [blockEquivIter_val_inl, iterFin_val] at hval
  have hi := i.isLt
  omega

/-- **The left block inclusion at the iterate's index.** -/
noncomputable def cpBlockInclIter (d : ℕ) : C(CP d, CP (d + (d + 1))) :=
  cpEmbed (sumInclLeft (blockEquivIter d)) (sumInclLeft_isometry (blockEquivIter d))

theorem sumInclLeft_conjTranspose_mul_iterMat (d : ℕ) :
    (sumInclLeft (blockEquivIter d))ᴴ * iterMat d (d + 1) = 0 := by
  rw [sumInclLeft_eq_coordIncl, iterMat_eq_coordIncl]
  exact coordIncl_conjTranspose_mul_of_disjoint fun i k => blockEquivIter_ne_iterFin d i k

theorem iterMat_conjTranspose_mul_sumInclLeft (d : ℕ) :
    (iterMat d (d + 1))ᴴ * sumInclLeft (blockEquivIter d) = 0 := by
  rw [sumInclLeft_eq_coordIncl, iterMat_eq_coordIncl]
  exact coordIncl_conjTranspose_mul_of_disjoint fun k i => (blockEquivIter_ne_iterFin d i k).symm

/-- **The bridge.**  The left block inclusion is homotopic to the `(d+1)`-fold
hyperplane inclusion, because their ranges are orthogonal.  Every statement here
lives at the index `d + (d + 1)`, so nothing is cast. -/
theorem homotopic_cpBlockInclIter (d : ℕ) :
    (cpBlockInclIter d).Homotopic
      (cpEmbed (iterMat d (d + 1)) (iterMat_isometry d (d + 1))) :=
  homotopic_cpEmbed_of_orthogonal (sumInclLeft_isometry (blockEquivIter d))
    (iterMat_isometry d (d + 1))
    (sumInclLeft_conjTranspose_mul_iterMat d) (iterMat_conjTranspose_mul_sumInclLeft d)

/-- Euler-class invariance at the iterate's index, the analogue of
`homotopic_classifyOne_blockIncl`. -/
theorem homotopic_classifyOne_blockInclIter {X : Type} [TopologicalSpace X] {d : ℕ}
    {p q : Bundle X (Fin (d + 1))} (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1)
    (e : BundleIso p q) :
    ((cpBlockInclIter d).comp (classifyOne p hp)).Homotopic
      ((cpBlockInclIter d).comp (classifyOne q hq)) :=
  homotopic_cpEmbed_same e (sumInclLeft_isometry (blockEquivIter d))
    (sumInclRight_isometry (blockEquivIter d))
    (sumInclLeft_conjTranspose_mul_right (blockEquivIter d))
    (sumInclRight_conjTranspose_mul_left (blockEquivIter d)) hp hq

end Iter

end Bundle

end CharClass
end GroupApproximation
