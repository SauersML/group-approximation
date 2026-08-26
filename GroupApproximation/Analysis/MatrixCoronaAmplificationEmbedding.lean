import GroupApproximation.Analysis.MatrixCoronaDedekindFinite

/-!
# Matrix-corona amplification as an embedding

For a finite nonempty index type `I`, this file constructs the canonical
nonunital star-algebra embedding

`CStarMatrix I I (NormMatrixCStarCorona X) → NormMatrixCStarCorona (I × X)`.

The map chooses bounded representatives entrywise, assembles their coordinate
matrices into matrices on `I × X n`, and then passes to the corona.  It is
independent of the representatives because an assembled sequence is null
exactly when each of its finitely many blocks is null.  The two implications
of that equivalence are the block bounds from
`MatrixCoronaDedekindFinite.lean`.

No MF hypothesis is used: this is an unconditional property of norm-matrix
coronas.  Nonemptiness of `I` is only needed to equip the target corona with
its C-star-algebra structure.
-/

namespace GroupApproximation
namespace MatrixCoronaAmplificationEmbedding

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

private abbrev LiftMatrix (I : Type) [Fintype I] [DecidableEq I]
    (X : ℕ → FiniteModel) :=
  I → I → BoundedMatrixSequence (fun n ↦ X n)

/-- Assemble a finite matrix of bounded sequences into a bounded sequence of
matrices on the product index. -/
def assembleSequence (a : LiftMatrix I X) :
    BoundedMatrixSequence (fun n ↦ I × X n) :=
  ⟨fun n ↦ MatrixCoronaFinite.assemble X a n,
    memℓp_infty ⟨∑ i : I, ∑ j : I, ‖a i j‖, by
      rintro _ ⟨n, rfl⟩
      exact MatrixCoronaFinite.norm_assemble_le X a n⟩⟩

omit [Nonempty I] [∀ n, Nonempty (X n)] in
@[simp] theorem assembleSequence_apply (a : LiftMatrix I X) (n : ℕ) :
    assembleSequence X a n = MatrixCoronaFinite.assemble X a n := rfl

omit [Nonempty I] [∀ n, Nonempty (X n)] in
@[simp] theorem block_assembleSequence (a : LiftMatrix I X)
    (i j : I) (n : ℕ) :
    MatrixCoronaFinite.block i j (assembleSequence X a n) = a i j n := rfl

omit [Nonempty I] [∀ n, Nonempty (X n)] in
theorem assembleSequence_sub (a b : LiftMatrix I X) :
    assembleSequence X (a - b) =
      assembleSequence X a - assembleSequence X b := by
  apply lp.ext
  funext n
  ext p q
  rfl

/-- Nullity of an assembled sequence is equivalent to entrywise nullity.
This is the representative-independence and faithfulness mechanism for the
amplification map. -/
theorem isNull_assembleSequence_iff (a : LiftMatrix I X) :
    IsNullMatrixSequence (fun n ↦ I × X n) cofinite (assembleSequence X a) ↔
      ∀ i j, IsNullMatrixSequence (fun n ↦ X n) cofinite (a i j) := by
  constructor
  · intro ha i j
    rw [IsNullMatrixSequence] at ha ⊢
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg (a i j n))
      (Eventually.of_forall fun n ↦ ?_) ha
    rw [← block_assembleSequence X a i j n]
    exact MatrixCoronaFinite.norm_block_le i j (assembleSequence X a n)
  · intro ha
    rw [IsNullMatrixSequence]
    refine squeeze_zero'
      (g := fun n ↦ ∑ i : I, ∑ j : I, ‖a i j n‖)
      (Eventually.of_forall fun n ↦ norm_nonneg (assembleSequence X a n))
      (Eventually.of_forall fun n ↦ ?_) ?_
    · calc
        ‖assembleSequence X a n‖
            ≤ ∑ i : I, ∑ j : I,
                ‖MatrixCoronaFinite.block i j (assembleSequence X a n)‖ :=
          MatrixCoronaFinite.norm_le_sum_blocks (assembleSequence X a n)
        _ = ∑ i : I, ∑ j : I, ‖a i j n‖ := by
          simp only [block_assembleSequence]
    · have hsum : Tendsto
          (fun n ↦ ∑ i : I, ∑ j : I, ‖a i j n‖) cofinite
          (nhds (∑ _i : I, ∑ _j : I, (0 : ℝ))) :=
        tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ ha i j
      simpa using hsum

/-- The target-corona class represented by an assembled matrix of lifts. -/
def coronaOfLifts (a : LiftMatrix I X) :
    NormMatrixCStarCorona (fun n ↦ I × X n) :=
  normMatrixCStarCoronaMk (fun n ↦ I × X n) (assembleSequence X a)

/-- Entrywise equality of source-corona classes implies equality after
assembly. -/
theorem coronaOfLifts_eq_of_mk_eq {a b : LiftMatrix I X}
    (h : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (a i j) =
      normMatrixCStarCoronaMk (fun n ↦ X n) (b i j)) :
    coronaOfLifts X a = coronaOfLifts X b := by
  unfold coronaOfLifts
  rw [← sub_eq_zero, ← map_sub, ← assembleSequence_sub,
    normMatrixCStarCoronaMk_eq_zero_iff,
    isNull_assembleSequence_iff]
  intro i j
  rw [← normMatrixCStarCoronaMk_eq_zero_iff]
  change normMatrixCStarCoronaMk (fun n ↦ X n) (a i j - b i j) = 0
  rw [map_sub, h i j, sub_self]

theorem coronaOfLifts_zero :
    coronaOfLifts X (0 : LiftMatrix I X) = 0 := by
  rw [coronaOfLifts, ← map_zero
    (normMatrixCStarCoronaMk (fun n ↦ I × X n))]
  congr 1
  apply lp.ext
  funext n
  ext p q

theorem coronaOfLifts_add (a b : LiftMatrix I X) :
    coronaOfLifts X (a + b) = coronaOfLifts X a + coronaOfLifts X b := by
  rw [coronaOfLifts, coronaOfLifts, coronaOfLifts, ← map_add]
  congr 1
  apply lp.ext
  funext n
  ext p q

theorem coronaOfLifts_smul (c : ℂ) (a : LiftMatrix I X) :
    coronaOfLifts X (c • a) = c • coronaOfLifts X a := by
  unfold coronaOfLifts
  have hseq : assembleSequence X (c • a) = c • assembleSequence X a := by
    apply lp.ext
    funext n
    ext p q
    rfl
  change normMatrixCStarCoronaQuotient (fun n ↦ I × X n)
      (assembleSequence X (c • a)) =
    c • normMatrixCStarCoronaQuotient (fun n ↦ I × X n)
      (assembleSequence X a)
  rw [hseq, map_smul]

theorem coronaOfLifts_mul (a b : LiftMatrix I X) :
    coronaOfLifts X (fun i j ↦ ∑ r : I, a i r * b r j) =
      coronaOfLifts X a * coronaOfLifts X b := by
  rw [coronaOfLifts, coronaOfLifts, coronaOfLifts, ← map_mul]
  congr 1
  apply lp.ext
  funext n
  exact (MatrixCoronaFinite.assemble_mul X a b n).symm

theorem coronaOfLifts_star (a : LiftMatrix I X) :
    coronaOfLifts X (fun i j ↦ star (a j i)) = star (coronaOfLifts X a) := by
  rw [coronaOfLifts, coronaOfLifts, normMatrixCStarCorona_star_mk]
  congr 1
  apply lp.ext
  funext n
  ext p q

/-- A fixed representative of each element of the source corona. -/
def representative (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) x

@[simp] theorem mk_representative
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (representative X x) = x :=
  Function.surjInv_eq (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) x

/-- The unconditional matrix-amplification map between norm-matrix coronas. -/
def matrixCoronaAmplification :
    CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n)) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ I × X n) where
  toFun P := coronaOfLifts X (fun i j ↦ representative X (P i j))
  map_zero' := by
    rw [← coronaOfLifts_zero X]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    simp
  map_add' P Q := by
    rw [← coronaOfLifts_add]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    rw [CStarMatrix.add_apply, Pi.add_apply, Pi.add_apply, map_add,
      mk_representative, mk_representative, mk_representative]
  map_mul' P Q := by
    rw [← coronaOfLifts_mul]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    rw [CStarMatrix.mul_apply, mk_representative, map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ by
      rw [map_mul, mk_representative, mk_representative]
  map_smul' c P := by
    change coronaOfLifts X (fun i j ↦ representative X ((c • P) i j)) =
      c • coronaOfLifts X (fun i j ↦ representative X (P i j))
    rw [← coronaOfLifts_smul]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    calc
      normMatrixCStarCoronaMk (fun n ↦ X n)
          (representative X ((c • P) i j))
          = (c • P) i j := mk_representative X _
      _ = c • P i j := CStarMatrix.smul_apply c P i j
      _ = c • normMatrixCStarCoronaMk (fun n ↦ X n)
          (representative X (P i j)) := by rw [mk_representative]
      _ = normMatrixCStarCoronaMk (fun n ↦ X n)
          (c • representative X (P i j)) :=
        (map_smul (normMatrixCStarCoronaQuotient (fun n ↦ X n)) c _).symm
  map_star' P := by
    rw [← coronaOfLifts_star]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    rw [CStarMatrix.star_apply, mk_representative,
      ← normMatrixCStarCorona_star_mk, mk_representative]

@[simp] theorem matrixCoronaAmplification_apply
    (P : CStarMatrix I I (NormMatrixCStarCorona (fun n ↦ X n))) :
    matrixCoronaAmplification X P =
      coronaOfLifts X (fun i j ↦ representative X (P i j)) := rfl

/-- The amplification map is injective.  An assembled null difference has
null `(i,j)` block, hence the corresponding source-corona entries agree. -/
theorem matrixCoronaAmplification_injective :
    Function.Injective (matrixCoronaAmplification (I := I) X) := by
  intro P Q hPQ
  ext i j
  let a : LiftMatrix I X := fun r s ↦ representative X (P r s)
  let b : LiftMatrix I X := fun r s ↦ representative X (Q r s)
  have hclass : coronaOfLifts X a = coronaOfLifts X b := hPQ
  have hamp : IsNullMatrixSequence (fun n ↦ I × X n) cofinite
      (assembleSequence X (a - b)) := by
    rw [assembleSequence_sub, ← normMatrixCStarCoronaMk_eq_zero_iff]
    change coronaOfLifts X a - coronaOfLifts X b = 0
    exact sub_eq_zero.mpr hclass
  have hentry := (isNull_assembleSequence_iff X (a - b)).mp hamp i j
  have hij : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (representative X (P i j) - representative X (Q i j)) := by
    simpa only [Pi.sub_apply, a, b] using hentry
  have hzero :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr hij
  rw [map_sub, mk_representative, mk_representative, sub_eq_zero] at hzero
  exact hzero

end

end MatrixCoronaAmplificationEmbedding
end GroupApproximation
