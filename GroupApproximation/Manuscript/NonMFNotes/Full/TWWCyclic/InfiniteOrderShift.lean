import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.BlockMatrix

/-!
# Cyclic shift block matrices

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), cyclic extension step, infinite-order case in which a
power of the extending element centralizes the subgroup.

For `p : ZMod N` and a matrix `A` on `W`, `shiftBlock p A` is the matrix on
`ZMod N × W` whose `(i, j)` block is `A` when `i + p = j` and `0` otherwise, that is
the tensor product of the cyclic shift by `p` with `A`. This file proves the algebra
of these matrices: product, difference, conjugate transpose, the norm bound and the
two trace formulas. Shifts by a nonzero residue have trace zero.
-/

namespace GroupApproximation.Full.TWWCyclic

open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- The cyclic shift by `p` tensored with `A`. -/
def shiftBlock {N : ℕ} {W : Type} (p : ZMod N) (A : Matrix W W ℂ) :
    Matrix (ZMod N × W) (ZMod N × W) ℂ :=
  blockMat fun i j : ZMod N => if i + p = j then A else 0

theorem norm_shiftBlock_le {N : ℕ} [NeZero N] {W : Type} [Fintype W] [DecidableEq W]
    (p : ZMod N) {A : Matrix W W ℂ} {c : ℝ} (hc : 0 ≤ c) (hA : ‖A‖ ≤ c) :
    ‖shiftBlock p A‖ ≤ c := by
  refine norm_blockMat_le (fun i j : ZMod N => if i + p = j then A else 0)
    (fun i j : ZMod N => i + p = j) hc (fun i j => ?_) (fun i j hne => ?_)
    (fun _ _ _ hj hj' => hj.symm.trans hj')
    (fun _ _ _ hi hi' => add_right_cancel (hi.trans hi'.symm))
  · show ‖if i + p = j then A else 0‖ ≤ c
    by_cases h : i + p = j
    · rw [if_pos h]
      exact hA
    · rw [if_neg h, norm_zero]
      exact hc
  · show i + p = j
    by_contra h
    exact hne (if_neg h)

theorem shiftBlock_mul {N : ℕ} [NeZero N] {W : Type} [Fintype W] (p q : ZMod N)
    (A B : Matrix W W ℂ) :
    shiftBlock p A * shiftBlock q B = shiftBlock (p + q) (A * B) := by
  show blockMat (fun i j : ZMod N => if i + p = j then A else 0) *
      blockMat (fun i j : ZMod N => if i + q = j then B else 0) =
    blockMat (fun i j : ZMod N => if i + (p + q) = j then A * B else 0)
  rw [blockMat_mul]
  refine congrArg blockMat (funext fun i => funext fun j => ?_)
  show ∑ l : ZMod N, (if i + p = l then A else 0) * (if l + q = j then B else 0) =
    if i + (p + q) = j then A * B else 0
  have hz : ∀ l ∈ (Finset.univ : Finset (ZMod N)), l ≠ i + p →
      (if i + p = l then A else 0) * (if l + q = j then B else 0) = 0 := by
    intro l _ hl
    rw [if_neg fun h => hl h.symm, Matrix.zero_mul]
  rw [Finset.sum_eq_single (i + p) hz (fun hn => absurd (Finset.mem_univ _) hn), if_pos rfl]
  by_cases hj : i + (p + q) = j
  · rw [if_pos hj, if_pos ((add_assoc i p q).trans hj)]
  · rw [if_neg hj, if_neg fun h => hj ((add_assoc i p q).symm.trans h), Matrix.mul_zero]

theorem shiftBlock_sub {N : ℕ} {W : Type} (p : ZMod N) (A B : Matrix W W ℂ) :
    shiftBlock p A - shiftBlock p B = shiftBlock p (A - B) := by
  show blockMat (fun i j : ZMod N => if i + p = j then A else 0) -
      blockMat (fun i j : ZMod N => if i + p = j then B else 0) =
    blockMat (fun i j : ZMod N => if i + p = j then A - B else 0)
  rw [blockMat_sub]
  refine congrArg blockMat (funext fun i => funext fun j => ?_)
  show (if i + p = j then A else 0) - (if i + p = j then B else 0) =
    if i + p = j then A - B else 0
  by_cases h : i + p = j
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, sub_zero]

theorem shiftBlock_conjTranspose {N : ℕ} {W : Type} (p : ZMod N) (A : Matrix W W ℂ) :
    (shiftBlock p A)ᴴ = shiftBlock (-p) Aᴴ := by
  show (blockMat fun i j : ZMod N => if i + p = j then A else 0)ᴴ =
    blockMat (fun i j : ZMod N => if i + -p = j then Aᴴ else 0)
  rw [blockMat_conjTranspose]
  refine congrArg blockMat (funext fun i => funext fun j => ?_)
  show (if j + p = i then A else 0)ᴴ = if i + -p = j then Aᴴ else 0
  by_cases h : j + p = i
  · have h' : i + -p = j := by
      rw [← h, add_neg_cancel_right]
    rw [if_pos h, if_pos h']
  · have h' : ¬(i + -p = j) := by
      intro h''
      apply h
      rw [← h'', neg_add_cancel_right]
    rw [if_neg h, if_neg h', Matrix.conjTranspose_zero]

/-- The shift by `0` has `N` times the trace of `A`. -/
theorem trace_shiftBlock_zero {N : ℕ} [NeZero N] {W : Type} [Fintype W] (A : Matrix W W ℂ) :
    Matrix.trace (shiftBlock (0 : ZMod N) A) = (N : ℂ) * Matrix.trace A := by
  calc Matrix.trace (shiftBlock (0 : ZMod N) A)
      = ∑ i : ZMod N, Matrix.trace (if i + 0 = i then A else 0) :=
        trace_blockMat fun i j : ZMod N => if i + 0 = j then A else 0
    _ = ∑ _i : ZMod N, Matrix.trace A :=
        Finset.sum_congr rfl fun i _ => by rw [if_pos (add_zero i)]
    _ = (N : ℂ) * Matrix.trace A := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- A shift by a nonzero residue has trace zero. -/
theorem trace_shiftBlock_of_ne {N : ℕ} [NeZero N] {W : Type} [Fintype W] {p : ZMod N}
    (hp : p ≠ 0) (A : Matrix W W ℂ) : Matrix.trace (shiftBlock p A) = 0 := by
  calc Matrix.trace (shiftBlock p A)
      = ∑ i : ZMod N, Matrix.trace (if i + p = i then A else 0) :=
        trace_blockMat fun i j : ZMod N => if i + p = j then A else 0
    _ = 0 := Finset.sum_eq_zero fun i _ => by
        rw [if_neg fun h => hp (add_left_cancel (h.trans (add_zero i).symm)),
          Matrix.trace_zero]

end GroupApproximation.Full.TWWCyclic
