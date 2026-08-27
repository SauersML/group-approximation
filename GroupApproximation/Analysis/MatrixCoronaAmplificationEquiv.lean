import GroupApproximation.Analysis.MatrixCoronaAmplificationEmbedding

/-!
# Matrix amplification of a norm-matrix corona

This completes the canonical identification

`M_I(∏ M_{X n}/⊕ M_{X n}) ≃⋆ₐ[ℂ] ∏ M_{I × X n}/⊕ M_{I × X n}`.

The forward map and its injectivity are constructed in
`MatrixCoronaAmplificationEmbedding`.  Surjectivity is obtained by choosing a
bounded representative in the amplified corona and taking its finitely many
coordinate blocks.  The block bound makes each block sequence bounded, while
assembling all the blocks recovers the original representative exactly.
-/

namespace GroupApproximation
namespace MatrixCoronaAmplificationEmbedding

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- The `(i,j)` blocks of a bounded amplified sequence form a bounded
sequence in the unamplified coordinates. -/
def blockSequence
    (a : BoundedMatrixSequence (fun n ↦ I × X n)) (i j : I) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  ⟨fun n ↦ MatrixCoronaFinite.block i j (a n),
    memℓp_infty ⟨‖a‖, by
      rintro _ ⟨n, rfl⟩
      exact (MatrixCoronaFinite.norm_block_le i j (a n)).trans
        (boundedMatrixSequence_coord_norm_le (fun n ↦ I × X n) a n)⟩⟩

omit [Nonempty I] [∀ n, Nonempty (X n)] in
@[simp] theorem blockSequence_apply
    (a : BoundedMatrixSequence (fun n ↦ I × X n)) (i j : I) (n : ℕ) :
    blockSequence X a i j n = MatrixCoronaFinite.block i j (a n) := rfl

omit [Nonempty I] [∀ n, Nonempty (X n)] in
/-- Assembling all block sequences recovers the amplified sequence. -/
theorem assembleSequence_blockSequence
    (a : BoundedMatrixSequence (fun n ↦ I × X n)) :
    assembleSequence X (fun i j ↦ blockSequence X a i j) = a := by
  apply lp.ext
  funext n
  ext p q
  rfl

/-- The canonical amplification map is onto. -/
theorem matrixCoronaAmplification_surjective :
    Function.Surjective (matrixCoronaAmplification (I := I) X) := by
  intro y
  obtain ⟨a, rfl⟩ :=
    normMatrixCStarCoronaMk_surjective (fun n ↦ I × X n) y
  let P : CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)) :=
    fun i j ↦ normMatrixCStarCoronaMk (fun n ↦ X n) (blockSequence X a i j)
  refine ⟨P, ?_⟩
  calc
    matrixCoronaAmplification X P =
        coronaOfLifts X (fun i j ↦ blockSequence X a i j) := by
      rw [matrixCoronaAmplification_apply]
      apply coronaOfLifts_eq_of_mk_eq X
      intro i j
      rw [mk_representative]
    _ = normMatrixCStarCoronaMk (fun n ↦ I × X n) a := by
      unfold coronaOfLifts
      rw [assembleSequence_blockSequence]

/-- Surjectivity forces the canonical nonunital map to preserve the unit. -/
theorem matrixCoronaAmplification_map_one :
    matrixCoronaAmplification (I := I) X 1 = 1 := by
  obtain ⟨x, hx⟩ := matrixCoronaAmplification_surjective (I := I) X 1
  let f := matrixCoronaAmplification (I := I) X
  calc
    f 1 = f 1 * 1 := (mul_one _).symm
    _ = f 1 * f x := by rw [hx]
    _ = f (1 * x) := (map_mul f 1 x).symm
    _ = f x := by rw [one_mul]
    _ = 1 := hx

/-- The canonical amplification as a unital star-algebra homomorphism. -/
def matrixCoronaAmplificationUnital :
    CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)) →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ I × X n) where
  toFun := matrixCoronaAmplification X
  map_one' := matrixCoronaAmplification_map_one X
  map_mul' := map_mul (matrixCoronaAmplification X)
  map_zero' := map_zero (matrixCoronaAmplification X)
  map_add' := map_add (matrixCoronaAmplification X)
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      map_smul, matrixCoronaAmplification_map_one]
  map_star' := map_star (matrixCoronaAmplification X)

/-- The canonical star-algebra isomorphism between matrices over the corona
and the corona of the amplified matrix sizes. -/
def matrixCoronaAmplificationEquiv :
    CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)) ≃⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ I × X n) :=
  StarAlgEquiv.ofBijective (matrixCoronaAmplificationUnital X)
    ⟨matrixCoronaAmplification_injective X,
      matrixCoronaAmplification_surjective X⟩

end

end MatrixCoronaAmplificationEmbedding
end GroupApproximation
