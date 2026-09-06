import GroupApproximation.CharClass.LIXVBundle
import GroupApproximation.CharClass.SliceVLinesY

/-!
# The lines of `V` as bundles

Lane `cc-lix-odd`, for `cc-steenrod`'s split relation.

`LIXVDecomposition` gives the lines as matrix families with their traces.
`splitRelation_of_sum` wants them as `Bundle` values, so each needs continuity and the
projection property as well.  `cc-steenrod` spotted that; the traces alone are half of what
a rank-one line has to carry.

Like `V` itself, every line factors through the projective base, so they all live over
`baseY dd` and no pullback appears anywhere.

**On the name.**  `cc-steenrod` landed `vLineY` for the same object in `SliceVLinesY`,
rooted first, while our messages crossed.  Two definitions of one name in one namespace is
a duplicate declaration, not an ambiguity, so the root would have failed outright.  The
definitions here are renamed to `vLineProj`, and the two facts are restated about **their**
`vLineY` at the foot, which is defeq to mine.  The name belongs to the file that claimed it
first.

**Each obligation is a separate lemma and the structures are assembled last.**  That is
`cc-steenrod`'s observation about this layer, and it matches the one failure in the
previous file: proving a structure's fields inline is what fights elaboration.

## Main results

* `trivLineY`, `hLineY`, `vLineProj` — the lines over the projective base.
* `isStarProjection_vLineProj`, `continuous_vLineProj` — the two obligations, separately.
* `vLineBundle` — **the lines as bundles**, with `sum_vLineBundle` the decomposition.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop.CPn

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The lines over the projective base -/

/-- The `b`-th tautological line's `H`-block, over the projective base. -/
def hLineProjBlock (b : HBlk dd) (y : baseY dd) : Matrix (HIdx dd) (HIdx dd) ℂ :=
  Matrix.blockDiagonal' fun b' : HBlk dd =>
    if b' = b then ((y b'.1 : CP (dd b'.1)) :
      Matrix (Fin (dd b'.1 + 1)) (Fin (dd b'.1 + 1)) ℂ) else 0

/-- The lines of `V`, over the projective base. -/
def vLineProj (b : Fin 3 ⊕ HBlk dd) (y : baseY dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  match b with
  | Sum.inl i => Matrix.fromBlocks (trivLine i) 0 0 0
  | Sum.inr b => Matrix.fromBlocks 0 0 0 (hLineProjBlock b y)

theorem vLineY_eq (b : Fin 3 ⊕ HBlk dd) (m : baseM dd) : vLineProj b m.2 = vLine b m := by
  cases b <;> rfl

/-! ## 2. The projection property -/

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

theorem isStarProjection_hLineYblock (b : HBlk dd) (y : baseY dd) :
    IsStarProjection (hLineProjBlock b y) := by
  constructor
  · show hLineProjBlock b y * hLineProjBlock b y = hLineProjBlock b y
    rw [hLineProjBlock, ← Matrix.blockDiagonal'_mul]
    refine congrArg Matrix.blockDiagonal' (funext fun b' => ?_)
    by_cases h : b' = b
    · rw [if_pos h]
      exact (isStarProjection_coe (y b'.1)).isIdempotentElem.eq
    · rw [if_neg h, Matrix.mul_zero]
  · show star (hLineProjBlock b y) = hLineProjBlock b y
    rw [Matrix.star_eq_conjTranspose, hLineProjBlock, Matrix.blockDiagonal'_conjTranspose]
    refine congrArg Matrix.blockDiagonal' (funext fun b' => ?_)
    by_cases h : b' = b
    · rw [if_pos h]
      exact conjTranspose_eq_of_isStarProjection (isStarProjection_coe (y b'.1))
    · rw [if_neg h, Matrix.conjTranspose_zero]

/-- Both lines are `fromBlocks` with one projection block and zeros; the two cases run the
same way, mirroring `isStarProjection_Vmat`. -/
theorem isStarProjection_vLineProj (b : Fin 3 ⊕ HBlk dd) (y : baseY dd) :
    IsStarProjection (vLineProj b y) := by
  cases b with
  | inl i =>
      have hP := isStarProjection_trivLine i
      constructor
      · show vLineProj (Sum.inl i) y * vLineProj (Sum.inl i) y = vLineProj (Sum.inl i) y
        show Matrix.fromBlocks (trivLine i) 0 0 (0 : Matrix (HIdx dd) (HIdx dd) ℂ) *
            Matrix.fromBlocks (trivLine i) 0 0 0 = _
        rw [Matrix.fromBlocks_multiply]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · simpa using hP.isIdempotentElem.eq
        · simp
        · simp
        · simp
      · show star (vLineProj (Sum.inl i) y) = vLineProj (Sum.inl i) y
        show star (Matrix.fromBlocks (trivLine i) 0 0
          (0 : Matrix (HIdx dd) (HIdx dd) ℂ)) = _
        rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · have : star (trivLine i) = trivLine i := hP.isSelfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
  | inr b =>
      have hP := isStarProjection_hLineYblock b y
      constructor
      · show vLineProj (Sum.inr b) y * vLineProj (Sum.inr b) y = vLineProj (Sum.inr b) y
        show Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 (hLineProjBlock b y) *
            Matrix.fromBlocks 0 0 0 (hLineProjBlock b y) = _
        rw [Matrix.fromBlocks_multiply]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simp
        · simpa using hP.isIdempotentElem.eq
      · show star (vLineProj (Sum.inr b) y) = vLineProj (Sum.inr b) y
        show star (Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
          (hLineProjBlock b y)) = _
        rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
        refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · exact Matrix.conjTranspose_zero
        · have : star (hLineProjBlock b y) = hLineProjBlock b y := hP.isSelfAdjoint.star_eq
          rwa [Matrix.star_eq_conjTranspose] at this

/-! ## 3. Continuity -/

theorem continuous_hLineYblock (b : HBlk dd) :
    Continuous (hLineProjBlock b (dd := dd)) :=
  continuous_blockDiagonal' fun b' => by
    by_cases h : b' = b
    · simp only [if_pos h]
      exact (continuous_coe (d := dd b'.1)).comp (continuous_apply b'.1)
    · simp only [if_neg h]
      exact continuous_const

theorem continuous_vLineProj (b : Fin 3 ⊕ HBlk dd) : Continuous (vLineProj b (dd := dd)) := by
  cases b with
  | inl i => exact continuous_const
  | inr b =>
      refine continuous_matrix fun p q => ?_
      cases p with
      | inl a => cases q <;> exact continuous_const
      | inr a =>
          cases q with
          | inl c => exact continuous_const
          | inr c =>
              exact (continuous_hLineYblock b).matrix_elem a c

/-! ## 4. The bundles -/

/-- **The lines of `V`, as bundles.** -/
def vLineBundle (b : Fin 3 ⊕ HBlk dd) : Bundle (baseY dd) (VIdx dd) where
  toFun := vLineProj b
  continuous_toFun := continuous_vLineProj b
  isStarProjection_toFun := isStarProjection_vLineProj b

@[simp] theorem coe_vLineBundle (b : Fin 3 ⊕ HBlk dd) :
    ⇑(vLineBundle b) = vLineProj (dd := dd) b := rfl

/-- **The decomposition, in bundle form.** -/
theorem sum_vLineBundle (y : baseY dd) :
    VmatY y = ∑ b : Fin 3 ⊕ HBlk dd, vLineBundle b y := by
  have h := Vmat_eq_sum_lines ((negEThree, y) : baseM dd)
  have hv : VmatY y = Vmat ((negEThree, y) : baseM dd) :=
    VmatY_eq ((negEThree, y) : baseM dd)
  rw [hv, h]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (vLineY_eq b ((negEThree, y) : baseM dd)).symm

/-! ## 5. The same two facts, about `cc-steenrod`'s `vLineY`

Their `vLineY b y` is `vLine b (negEThree, y)`, which is definitionally the lines above, so
each of these is the corresponding fact with no transport. -/

theorem continuous_vLineY (b : Fin 3 ⊕ HBlk dd) :
    Continuous (vLineY (dd := dd) b) := continuous_vLineProj b

theorem isStarProjection_vLineY (b : Fin 3 ⊕ HBlk dd) (y : baseY dd) :
    IsStarProjection (vLineY b y) := isStarProjection_vLineProj b y

/-- **`cc-steenrod`'s lines as bundles**, under their name. -/
def vLineYBundle (b : Fin 3 ⊕ HBlk dd) : Bundle (baseY dd) (VIdx dd) where
  toFun := vLineY b
  continuous_toFun := continuous_vLineY b
  isStarProjection_toFun := isStarProjection_vLineY b

end GroupApproximation.CharClass
