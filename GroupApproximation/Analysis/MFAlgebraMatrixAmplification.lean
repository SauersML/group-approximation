import GroupApproximation.Analysis.MatrixCoronaDedekindFinite

/-!
# Matrix amplifications of MF algebras are MF

For a positive integer `k`, this file constructs the faithful map

`M_k(Q_X) → Q_(k × X)`

needed by the reduced-product lemma in `mf_recognition_complexity.tex`.
An entry of a matrix over the corona is represented by a bounded matrix
sequence.  At every coordinate the `k²` representatives are assembled into
one block matrix indexed by `Fin k × X n`.  Different choices of
representatives have blockwise-null difference; the finite block estimate from
`StablyFiniteAmplification` makes the assembled difference null.  Conversely,
nullity of an assembled sequence implies nullity of each block, which gives
injectivity.

The construction is nonunital only because the ambient MF definition permits
nonunital embeddings.  The amplification map itself preserves the unit.
-/

namespace GroupApproximation
namespace MFAlgebraMatrixAmplification

open Filter Matrix
open AmplifiedBlocks
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

variable {k : ℕ} [Nonempty (Fin k)]
  (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

private abbrev LiftMatrix (k : ℕ) (X : ℕ → FiniteModel) :=
  Fin k → Fin k → BoundedMatrixSequence (fun n ↦ X n)

/-- Assemble a finite matrix of bounded sequences into one bounded sequence of
amplified matrices. -/
def assembleSequence (a : LiftMatrix k X) :
    BoundedMatrixSequence (fun n ↦ ampModel k (X n)) :=
  ⟨fun n ↦ MatrixCoronaFinite.assemble X a n,
    memℓp_infty ⟨∑ i : Fin k, ∑ j : Fin k, ‖a i j‖, by
      rintro _ ⟨n, rfl⟩
      exact MatrixCoronaFinite.norm_assemble_le X a n⟩⟩

omit [Nonempty (Fin k)] [∀ n, Nonempty (X n)] in
@[simp] theorem assembleSequence_apply (a : LiftMatrix k X) (n : ℕ) :
    assembleSequence X a n = MatrixCoronaFinite.assemble X a n := rfl

omit [Nonempty (Fin k)] [∀ n, Nonempty (X n)] in
@[simp] theorem block_assembleSequence (a : LiftMatrix k X)
    (i j : Fin k) (n : ℕ) :
    StablyFiniteAmplification.block i j (assembleSequence X a n) = a i j n :=
  rfl

/-- The corona class represented by an assembled matrix of lifts. -/
def coronaOfLifts (a : LiftMatrix k X) :
    NormMatrixCStarCorona (fun n ↦ ampModel k (X n)) :=
  normMatrixCStarCoronaMk (fun n ↦ ampModel k (X n)) (assembleSequence X a)

/-- Entrywise equality of corona classes implies equality after assembly. -/
theorem coronaOfLifts_eq_of_mk_eq {a b : LiftMatrix k X}
    (h : ∀ i j, normMatrixCStarCoronaMk (fun n ↦ X n) (a i j) =
      normMatrixCStarCoronaMk (fun n ↦ X n) (b i j)) :
    coronaOfLifts X a = coronaOfLifts X b := by
  rw [← sub_eq_zero, ← map_sub,
    normMatrixCStarCoronaMk_eq_zero_iff]
  apply StablyFiniteAmplification.tendsto_norm_of_forall_block
  intro i j
  have hij : IsNullMatrixSequence (fun n ↦ X n) cofinite (a i j - b i j) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, h i j, sub_self]
  simpa [assembleSequence, StablyFiniteAmplification.block] using hij

theorem coronaOfLifts_zero :
    coronaOfLifts X (0 : LiftMatrix k X) = 0 := by
  rw [coronaOfLifts, ← map_zero (normMatrixCStarCoronaMk
    (fun n ↦ ampModel k (X n)))]
  congr 1
  apply lp.ext
  funext n
  ext p q
  rfl

theorem coronaOfLifts_add (a b : LiftMatrix k X) :
    coronaOfLifts X (a + b) = coronaOfLifts X a + coronaOfLifts X b := by
  rw [coronaOfLifts, coronaOfLifts, coronaOfLifts, ← map_add]
  congr 1
  apply lp.ext
  funext n
  ext p q
  rfl

theorem coronaOfLifts_smul (c : ℂ) (a : LiftMatrix k X) :
    coronaOfLifts X (c • a) = c • coronaOfLifts X a := by
  rw [coronaOfLifts, coronaOfLifts,
    map_smul (normMatrixCStarCoronaQuotient (fun n ↦ ampModel k (X n)))]
  congr 1
  apply lp.ext
  funext n
  ext p q
  rfl

theorem coronaOfLifts_mul (a b : LiftMatrix k X) :
    coronaOfLifts X (fun i j ↦ ∑ r : Fin k, a i r * b r j) =
      coronaOfLifts X a * coronaOfLifts X b := by
  rw [coronaOfLifts, coronaOfLifts, coronaOfLifts, ← map_mul]
  congr 1
  apply lp.ext
  funext n
  exact (MatrixCoronaFinite.assemble_mul X a b n).symm

theorem coronaOfLifts_star (a : LiftMatrix k X) :
    coronaOfLifts X (fun i j ↦ star (a j i)) = star (coronaOfLifts X a) := by
  rw [coronaOfLifts, coronaOfLifts, normMatrixCStarCorona_star_mk]
  congr 1
  apply lp.ext
  funext n
  ext p q
  rfl

/-- A fixed representative of each element of the source corona. -/
def representative (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  Function.surjInv (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) x

@[simp] theorem mk_representative
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    normMatrixCStarCoronaMk (fun n ↦ X n) (representative X x) = x :=
  Function.surjInv_eq (normMatrixCStarCoronaMk_surjective (fun n ↦ X n)) x

/-- The matrix amplification map between norm-matrix coronas. -/
def matrixCoronaHom :
    CStarMatrix (Fin k) (Fin k)
        (NormMatrixCStarCorona (fun n ↦ X n)) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ ampModel k (X n)) where
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
    rw [map_add, mk_representative, mk_representative, mk_representative]
    rfl
  map_mul' P Q := by
    rw [← coronaOfLifts_mul]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    rw [map_sum, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ ↦ by
      rw [map_mul, mk_representative, mk_representative, mk_representative]
  map_smul' c P := by
    rw [← coronaOfLifts_smul]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    rw [map_smul (normMatrixCStarCoronaQuotient (fun n ↦ X n)),
      mk_representative, mk_representative]
    rfl
  map_star' P := by
    rw [← coronaOfLifts_star]
    apply coronaOfLifts_eq_of_mk_eq X
    intro i j
    rw [normMatrixCStarCorona_star_mk, mk_representative,
      mk_representative, CStarMatrix.star_apply]

@[simp] theorem matrixCoronaHom_apply
    (P : CStarMatrix (Fin k) (Fin k)
      (NormMatrixCStarCorona (fun n ↦ X n))) :
    matrixCoronaHom X P =
      coronaOfLifts X (fun i j ↦ representative X (P i j)) := rfl

/-- The amplification map is faithful: equality of assembled classes makes
each block difference null, so every source-corona entry agrees. -/
theorem matrixCoronaHom_injective : Function.Injective (matrixCoronaHom X) := by
  intro P Q hPQ
  apply CStarMatrix.ext
  intro i j
  have hamp : IsNullMatrixSequence (fun n ↦ ampModel k (X n)) cofinite
      (assembleSequence X (fun r s ↦ representative X (P r s)) -
        assembleSequence X (fun r s ↦ representative X (Q r s))) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub,
      ← matrixCoronaHom_apply, ← matrixCoronaHom_apply, hPQ, sub_self]
  have hblock := StablyFiniteAmplification.tendsto_norm_block
    (fun n ↦
      (assembleSequence X (fun r s ↦ representative X (P r s)) -
        assembleSequence X (fun r s ↦ representative X (Q r s))) n)
    hamp i j
  have hij : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (representative X (P i j) - representative X (Q i j)) := by
    simpa [assembleSequence, StablyFiniteAmplification.block] using hblock
  have hzero := (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr hij
  rw [map_sub, mk_representative, mk_representative, sub_eq_zero] at hzero
  exact hzero

/-! ## MF permanence -/

/-- A positive finite matrix amplification of an MF-embeddable C-star algebra
is again MF-embeddable. -/
theorem hasMFEmbedding_cstarMatrix
    {A : Type u} [CStarAlgebra A] (hA : HasMFEmbedding A) :
    HasMFEmbedding (CStarMatrix (Fin k) (Fin k) A) := by
  rcases hA with ⟨X, hne, hpos, hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  have hampne : ∀ n, Nonempty (ampModel k (X n)) := fun _ ↦ inferInstance
  have hamppos : ∀ n, 0 < Fintype.card (ampModel k (X n)) := fun n ↦ by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos (Fintype.card_pos_iff.mpr inferInstance) (hpos n)
  have hampmono : StrictMono (fun n ↦ Fintype.card (ampModel k (X n))) := by
    intro m n hmn
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_lt_mul_left (Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (Fin k)))).mpr (hmono hmn)
  let E : CStarMatrix (Fin k) (Fin k) A →⋆ₙₐ[ℂ]
      CStarMatrix (Fin k) (Fin k)
        (NormMatrixCStarCorona (fun n ↦ X n)) := CStarMatrix.mapₙₐ e
  have hE : Function.Injective E := by
    intro P Q hPQ
    ext i j
    apply he
    exact congrArg (fun M : CStarMatrix (Fin k) (Fin k)
      (NormMatrixCStarCorona (fun n ↦ X n)) ↦ M i j) hPQ
  exact ⟨fun n ↦ ampModel k (X n), hampne, hamppos, hampmono,
    (matrixCoronaHom X).comp E, matrixCoronaHom_injective X |>.comp hE⟩

/-- The manuscript's second reduced-product permanence assertion. -/
theorem isMFAlgebra_cstarMatrix
    {A : Type u} [CStarAlgebra A] (hA : IsMFAlgebra A) :
    IsMFAlgebra (CStarMatrix (Fin k) (Fin k) A) := by
  letI : TopologicalSpace.SeparableSpace A := hA.1
  exact ⟨inferInstance, hasMFEmbedding_cstarMatrix hA.2⟩

end

end MFAlgebraMatrixAmplification
end GroupApproximation
