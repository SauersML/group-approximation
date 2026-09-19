import GroupApproximation.CharClass.LIXVBundle
import GroupApproximation.CharClass.SliceVLinesY

/-!
# The lines of `V` as bundles

Lane `cc-lix-odd`, for `cc-steenrod`'s split relation.

`splitRelation_of_sum` consumes the **summands** as `Bundle` values, not only the total
bundle, so each line needs continuity and the projection property.  `LIXVDecomposition`
gave the lines and their traces; those are half of what a rank-one line carries.
`cc-steenrod` spotted the gap.

## One definition of the lines, and it is not this file's

`cc-steenrod`'s `SliceVLinesY.vLineY` is the lines over the projective base, landed and
root-wired first.  This file had its own, under the same name and in the same namespace,
which in one environment is a **duplicate declaration**: the root fails outright rather
than choosing.  Both probed green because neither imported the other.

The definition is theirs.  This file keeps none of its own, imports theirs, and proves the
two obligations about it directly, going through `vLine` per block, since `vLineY b y` is
`vLine b (negEThree, y)` by definition.  Anything else would leave two spellings of one
object, which is the failure this fleet has spent the night avoiding.

## Main results

* `isStarProjection_vLineY`, `continuous_vLineY` — the two obligations, separately, about
  `cc-steenrod`'s lines.
* `vLineYBundle` — **the lines as bundles**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The trivial summand -/

theorem isStarProjection_trivLine (i : Fin 3) : IsStarProjection (trivLine i) := by
  constructor
  · show trivLine i * trivLine i = trivLine i
    ext a c
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases h : a = i <;> by_cases h' : c = i <;> simp [trivLine, h, h']
    · intro d _ hne
      by_cases h : a = i <;> simp [trivLine, h, hne]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  · show star (trivLine i) = trivLine i
    rw [Matrix.star_eq_conjTranspose]
    ext a c
    simp only [Matrix.conjTranspose_apply, trivLine]
    by_cases h : c = i <;> by_cases h' : a = i <;> simp [h, h']

/-! ## 2. The `H` block at a constant sphere coordinate -/

theorem isStarProjection_hLine (b : HBlk dd) (m : baseM dd) :
    IsStarProjection (hLine b m) := by
  constructor
  · show hLine b m * hLine b m = hLine b m
    rw [hLine, ← Matrix.blockDiagonal'_mul]
    refine congrArg Matrix.blockDiagonal' (funext fun b' => ?_)
    by_cases h : b' = b
    · rw [if_pos h]
      exact (isStarProjection_coe (m.2 b'.1)).isIdempotentElem.eq
    · rw [if_neg h, Matrix.mul_zero]
  · show star (hLine b m) = hLine b m
    rw [Matrix.star_eq_conjTranspose, hLine, Matrix.blockDiagonal'_conjTranspose]
    refine congrArg Matrix.blockDiagonal' (funext fun b' => ?_)
    by_cases h : b' = b
    · rw [if_pos h]
      exact conjTranspose_eq_of_isStarProjection (isStarProjection_coe (m.2 b'.1))
    · rw [if_neg h, Matrix.conjTranspose_zero]

theorem continuous_hLine_const (b : HBlk dd) :
    Continuous fun y : baseY dd => hLine b ((negEThree, y) : baseM dd) := by
  show Continuous fun y : baseY dd => Matrix.blockDiagonal' fun b' : HBlk dd =>
    if b' = b then ((y b'.1 : CP (dd b'.1)) :
      Matrix (Fin (dd b'.1 + 1)) (Fin (dd b'.1 + 1)) ℂ) else 0
  refine continuous_blockDiagonal' fun b' => ?_
  by_cases h : b' = b
  · simp only [if_pos h]
    exact (continuous_coe (d := dd b'.1)).comp (continuous_apply b'.1)
  · simp only [if_neg h]
    exact continuous_const

/-! ## 3. The two obligations, about `cc-steenrod`'s lines -/

/-- **Each line is a star projection.**  Both cases are `fromBlocks` with one projection
block and zeros, run exactly as `isStarProjection_Vmat`. -/
theorem isStarProjection_vLineY (b : Fin 3 ⊕ HBlk dd) (y : baseY dd) :
    IsStarProjection (vLineY b y) := by
  cases b with
  | inl i =>
      have hP := isStarProjection_trivLine i
      constructor
      · show Matrix.fromBlocks (trivLine i) 0 0 (0 : Matrix (HIdx dd) (HIdx dd) ℂ) *
            Matrix.fromBlocks (trivLine i) 0 0 0 = _
        rw [Matrix.fromBlocks_multiply]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · simpa using hP.isIdempotentElem.eq
        · simp
        · simp
        · simp
      · show star (Matrix.fromBlocks (trivLine i) 0 0
          (0 : Matrix (HIdx dd) (HIdx dd) ℂ)) = _
        rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · have : star (trivLine i) = trivLine i := hP.isSelfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
  | inr b =>
      have hP := isStarProjection_hLine b ((negEThree, y) : baseM dd)
      constructor
      · show Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
            (hLine b ((negEThree, y) : baseM dd)) *
            Matrix.fromBlocks 0 0 0 (hLine b ((negEThree, y) : baseM dd)) = _
        rw [Matrix.fromBlocks_multiply]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp
        · simpa using hP.isIdempotentElem.eq
      · show star (Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
          (hLine b ((negEThree, y) : baseM dd))) = _
        rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · have : star (hLine b ((negEThree, y) : baseM dd))
              = hLine b ((negEThree, y) : baseM dd) := hP.isSelfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this

/-- **Each line is continuous.**  The trivial summand is constant; the block one is the
block-diagonal of a single tautological coordinate. -/
theorem continuous_vLineY (b : Fin 3 ⊕ HBlk dd) :
    Continuous (vLineY (dd := dd) b) := by
  cases b with
  | inl i => exact continuous_const
  | inr b =>
      refine continuous_matrix fun p q => ?_
      cases p with
      | inl a => cases q <;> exact continuous_const
      | inr a =>
          cases q with
          | inl c => exact continuous_const
          | inr c => exact (continuous_hLine_const b).matrix_elem a c

/-! ## 4. The bundles -/

/-- **The lines of `V`, as bundles**, over the same base as `vBundleY`. -/
def vLineYBundle (b : Fin 3 ⊕ HBlk dd) : Bundle (baseY dd) (VIdx dd) where
  toFun := vLineY b
  continuous_toFun := continuous_vLineY b
  isStarProjection_toFun := isStarProjection_vLineY b

@[simp] theorem coe_vLineYBundle (b : Fin 3 ⊕ HBlk dd) :
    ⇑(vLineYBundle b) = vLineY (dd := dd) b := rfl

end GroupApproximation.CharClass
