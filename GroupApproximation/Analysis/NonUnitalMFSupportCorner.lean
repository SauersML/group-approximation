import GroupApproximation.Analysis.CollapseDiscardCoordinates
import GroupApproximation.Analysis.CornerMatrixEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# The support corner of a nonunital MF embedding

Let `e : A →⋆ₙₐ Q` be an injective, possibly nonunital, star
homomorphism from a unital C-star algebra to a norm-matrix corona.  Its support
`p = e(1)` is a nonzero projection, every `e(a)` lies in the algebraic corner
`p Q p`, and a projection lift `(P_n)` of `p` is nonzero at infinitely many
coordinates.  Moreover, if `(x_n)` lifts `e(a)`, then `(P_n x_n P_n)` is
another lift of the same element.  These are the exact algebraic and cofinite
parts of unitalization by a support corner.

The file also enumerates the *entire* nonzero support in increasing order and
constructs the finite matrix index type of each projection range.  Its
cardinality is proved equal to the projection rank and hence positive.

This file deliberately stops before claiming a unital matrix-corona
embedding.  What remains is to bundle coordinate compression into a bounded
sequence map, descend it through cofinite null sequences as a star-algebra
homomorphism, and prove that nullity of the relabelled corner sequence reflects
nullity of the original supported sequence.  The exact range theorem proved
below is the set-theoretic input to that last implication, but is not itself an
injectivity proof.

The projection-lifting and coordinate-compression ingredients come from
`CollapseProjectionLift` and `PrintedCornerCompression`; the missing object is
their exact sequence-level, cofinite-corona assembly.
-/

namespace GroupApproximation
namespace NonUnitalMFSupportCorner

open Filter Matrix Topology
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-! ## Increasing enumeration of an infinite subset of `ℕ` -/

/-- The least member of an infinite subset of `ℕ`. -/
noncomputable def leastMember (S : Set ℕ) (hS : S.Infinite) : ℕ :=
  by
    classical
    exact Nat.find hS.nonempty

theorem leastMember_mem (S : Set ℕ) (hS : S.Infinite) :
    leastMember S hS ∈ S := by
  classical
  exact Nat.find_spec hS.nonempty

theorem leastMember_le (S : Set ℕ) (hS : S.Infinite)
    {n : ℕ} (hn : n ∈ S) : leastMember S hS ≤ n := by
  classical
  exact Nat.find_min' hS.nonempty hn

/-- The least member of `S` strictly above `n`. -/
noncomputable def nextMember (S : Set ℕ) (hS : S.Infinite) (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (Set.Infinite.exists_gt hS n)

theorem nextMember_mem (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    nextMember S hS n ∈ S := by
  classical
  exact (Nat.find_spec (Set.Infinite.exists_gt hS n)).1

theorem lt_nextMember (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    n < nextMember S hS n := by
  classical
  exact (Nat.find_spec (Set.Infinite.exists_gt hS n)).2

theorem nextMember_le (S : Set ℕ) (hS : S.Infinite) {n k : ℕ}
    (hk : k ∈ S) (hnk : n < k) : nextMember S hS n ≤ k := by
  classical
  exact Nat.find_min' (Set.Infinite.exists_gt hS n) ⟨hk, hnk⟩

/-- The increasing enumeration of an infinite subset of `ℕ`: start at its
least member and repeatedly take the least larger member. -/
noncomputable def increasingEnumeration (S : Set ℕ) (hS : S.Infinite) :
    ℕ → ℕ :=
  fun n ↦ Nat.rec (leastMember S hS)
    (fun _ previous ↦ nextMember S hS previous) n

@[simp]
theorem increasingEnumeration_zero (S : Set ℕ) (hS : S.Infinite) :
    increasingEnumeration S hS 0 = leastMember S hS :=
  rfl

@[simp]
theorem increasingEnumeration_succ (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    increasingEnumeration S hS (n + 1) =
      nextMember S hS (increasingEnumeration S hS n) :=
  rfl

theorem increasingEnumeration_mem (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    increasingEnumeration S hS n ∈ S := by
  induction n with
  | zero => exact leastMember_mem S hS
  | succ n _ =>
      rw [increasingEnumeration_succ]
      exact nextMember_mem S hS _

theorem increasingEnumeration_strictMono (S : Set ℕ) (hS : S.Infinite) :
    StrictMono (increasingEnumeration S hS) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [increasingEnumeration_succ]
  exact lt_nextMember S hS _

/-- The enumeration covers the entire set, not merely an infinite subset.
This exact range statement is what later makes restriction to the relabelled
coordinates reflect cofinite nullity on supported matrix families. -/
theorem range_increasingEnumeration (S : Set ℕ) (hS : S.Infinite) :
    Set.range (increasingEnumeration S hS) = S := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨n, rfl⟩
    exact increasingEnumeration_mem S hS n
  · intro k hk
    let f : ℕ → ℕ := increasingEnumeration S hS
    have hfmono : StrictMono f := increasingEnumeration_strictMono S hS
    have hex : ∃ n, k ≤ f n := ⟨k, hfmono.id_le k⟩
    refine ⟨Nat.find hex, ?_⟩
    apply le_antisymm ?_ (Nat.find_spec hex)
    by_cases hzero : Nat.find hex = 0
    · rw [hzero]
      change increasingEnumeration S hS 0 ≤ k
      rw [increasingEnumeration_zero]
      exact leastMember_le S hS hk
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hminimal : ¬ k ≤ f n := Nat.find_min hex (by omega)
      have hnlt : f n < k := Nat.lt_of_not_ge hminimal
      change increasingEnumeration S hS n < k at hnlt
      rw [hn]
      change increasingEnumeration S hS (n + 1) ≤ k
      rw [increasingEnumeration_succ]
      exact nextMember_le S hS hk hnlt

/-! ## Cofinite nullity along the full-support enumeration -/

/-- A scalar sequence supported on `S` tends to zero exactly when its
restriction to the increasing enumeration of all of `S` tends to zero.

The reverse implication uses the exact range equality above.  Merely choosing
an arbitrary infinite subsequence of `S` would not suffice. -/
theorem scalar_tendsto_zero_iff_increasingEnumeration
    (S : Set ℕ) (hS : S.Infinite) (r : ℕ → ℝ)
    (hsupport : ∀ n, n ∉ S → r n = 0) :
    Tendsto r atTop (nhds 0) ↔
      Tendsto (fun k ↦ r (increasingEnumeration S hS k)) atTop (nhds 0) := by
  constructor
  · intro hr
    exact hr.comp (increasingEnumeration_strictMono S hS).tendsto_atTop
  · intro hr
    rw [Metric.tendsto_atTop] at hr ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := hr ε hε
    refine ⟨increasingEnumeration S hS K, ?_⟩
    intro n hn
    by_cases hnS : n ∈ S
    · have hnrange : n ∈ Set.range (increasingEnumeration S hS) := by
        rw [range_increasingEnumeration S hS]
        exact hnS
      obtain ⟨k, rfl⟩ := hnrange
      apply hK k
      by_contra hnot
      exact (not_lt_of_ge hn)
        ((increasingEnumeration_strictMono S hS) (Nat.lt_of_not_ge hnot))
    · rw [hsupport n hnS]
      simpa only [dist_self] using hε

/-- Reindex a bounded matrix family along an arbitrary map.  Boundedness is
inherited from the original family. -/
def reindexBoundedMatrixSequence (φ : ℕ → ℕ)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    BoundedMatrixSequence (fun k ↦ Y (φ k)) :=
  ⟨fun k ↦ x (φ k), memℓp_infty ⟨‖x‖, by
    rintro _ ⟨k, rfl⟩
    change ‖(x (φ k) : Matrix (Y (φ k)) (Y (φ k)) ℂ)‖ ≤ ‖x‖
    exact boundedMatrixSequence_coord_norm_le (fun n ↦ Y n) x (φ k)⟩⟩

omit [∀ n, Nonempty (Y n)] in
@[simp] theorem reindexBoundedMatrixSequence_apply (φ : ℕ → ℕ)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) (k : ℕ) :
    (reindexBoundedMatrixSequence Y φ x k : Matrix (Y (φ k)) (Y (φ k)) ℂ) =
      x (φ k) :=
  rfl

omit [∀ n, Nonempty (Y n)] in
/-- Cofinite nullity of a supported bounded matrix family is equivalent to
cofinite nullity after relabelling by the full increasing enumeration of its
support. -/
theorem isNull_reindex_iff_of_supported
    (S : Set ℕ) (hS : S.Infinite)
    (x : BoundedMatrixSequence (fun n ↦ Y n))
    (hsupport : ∀ n, n ∉ S →
      (x n : Matrix (Y n) (Y n) ℂ) = 0) :
    IsNullMatrixSequence (fun n ↦ Y n) cofinite x ↔
      IsNullMatrixSequence (fun k ↦ Y (increasingEnumeration S hS k)) cofinite
        (reindexBoundedMatrixSequence Y (increasingEnumeration S hS) x) := by
  change Tendsto (fun n ↦ ‖(x n : Matrix (Y n) (Y n) ℂ)‖) cofinite (nhds 0) ↔
    Tendsto (fun k ↦
      ‖(x (increasingEnumeration S hS k) :
        Matrix (Y (increasingEnumeration S hS k))
          (Y (increasingEnumeration S hS k)) ℂ)‖) cofinite (nhds 0)
  rw [Nat.cofinite_eq_atTop]
  apply scalar_tendsto_zero_iff_increasingEnumeration S hS
  intro n hn
  rw [hsupport n hn, norm_zero]

/-! ## Relabelling the nonzero coordinates of a projection lift -/

/-- The nonzero coordinate support of a bounded matrix family. -/
def nonzeroSupport (P : BoundedMatrixSequence (fun n ↦ Y n)) : Set ℕ :=
  {n | (P n : Matrix (Y n) (Y n) ℂ) ≠ 0}

/-- The increasing enumeration of every nonzero coordinate of a nonzero
corona representative. -/
noncomputable def supportRelabelling
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) : ℕ → ℕ :=
  increasingEnumeration (nonzeroSupport Y P)
    (CollapseDiscardCoordinates.support_infinite_of_mk_ne_zero Y P hne)

theorem supportRelabelling_strictMono
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    StrictMono (supportRelabelling Y P hne) :=
  increasingEnumeration_strictMono _ _

theorem supportRelabelling_ne_zero
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    (P (supportRelabelling Y P hne k) :
      Matrix (Y (supportRelabelling Y P hne k))
        (Y (supportRelabelling Y P hne k)) ℂ) ≠ 0 := by
  show supportRelabelling Y P hne k ∈ nonzeroSupport Y P
  exact increasingEnumeration_mem _ _ k

theorem range_supportRelabelling
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    Set.range (supportRelabelling Y P hne) = nonzeroSupport Y P :=
  range_increasingEnumeration _ _

/-- The relabelling, with its support-membership proof attached, is a
surjection onto the full nonzero support. -/
theorem supportRelabelling_surjective
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    Function.Surjective (fun k ↦
      (⟨supportRelabelling Y P hne k,
        supportRelabelling_ne_zero Y P hne k⟩ :
        {n : ℕ // n ∈ nonzeroSupport Y P})) := by
  intro n
  have hnrange : n.1 ∈ Set.range (supportRelabelling Y P hne) := by
    rw [range_supportRelabelling Y P hne]
    exact n.2
  obtain ⟨k, hk⟩ := hnrange
  exact ⟨k, Subtype.ext hk⟩

/-- Reindex a bounded matrix family along every nonzero coordinate of `P`. -/
def supportReindex
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    BoundedMatrixSequence (fun k ↦ Y (supportRelabelling Y P hne k)) :=
  reindexBoundedMatrixSequence Y (supportRelabelling Y P hne) x

@[simp]
theorem supportReindex_apply
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) (k : ℕ) :
    (supportReindex Y P hne x k :
      Matrix (Y (supportRelabelling Y P hne k))
        (Y (supportRelabelling Y P hne k)) ℂ) =
      x (supportRelabelling Y P hne k) :=
  rfl

/-- A family which vanishes wherever `P` vanishes is cofinite-null exactly
when its full-support relabelling is cofinite-null. -/
theorem isNull_supportReindex_iff
    (P x : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (hsupport : ∀ n, (P n : Matrix (Y n) (Y n) ℂ) = 0 →
      (x n : Matrix (Y n) (Y n) ℂ) = 0) :
    IsNullMatrixSequence (fun n ↦ Y n) cofinite x ↔
      IsNullMatrixSequence (fun k ↦ Y (supportRelabelling Y P hne k)) cofinite
        (supportReindex Y P hne x) := by
  apply isNull_reindex_iff_of_supported Y (nonzeroSupport Y P)
    (CollapseDiscardCoordinates.support_infinite_of_mk_ne_zero Y P hne) x
  intro n hn
  apply hsupport n
  simpa [nonzeroSupport] using hn

omit [∀ n, Nonempty (Y n)] in
/-- Coordinate compression by `P` vanishes at every zero coordinate of `P`. -/
theorem compressFamily_eq_zero_of_projection_eq_zero
    (P x : BoundedMatrixSequence (fun n ↦ Y n)) (n : ℕ)
    (hzero : (P n : Matrix (Y n) (Y n) ℂ) = 0) :
    ((P * x * P) n : Matrix (Y n) (Y n) ℂ) = 0 := by
  change (P n : Matrix (Y n) (Y n) ℂ) * x n * P n = 0
  rw [hzero, Matrix.zero_mul, Matrix.zero_mul]

/-- Hence cofinite nullity of a compressed family is reflected exactly by
its full-support relabelling. -/
theorem isNull_compressFamily_supportReindex_iff
    (P x : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    IsNullMatrixSequence (fun n ↦ Y n) cofinite (P * x * P) ↔
      IsNullMatrixSequence (fun k ↦ Y (supportRelabelling Y P hne k)) cofinite
        (supportReindex Y P hne (P * x * P)) :=
  isNull_supportReindex_iff Y P (P * x * P) hne
    (compressFamily_eq_zero_of_projection_eq_zero Y P x)

/-! ## The finite projection-range models -/

open PrintedCornerCompression

theorem cornerCompression_zero
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) :
    cornerCompression hP (0 : Matrix Z Z ℂ) = 0 := by
  ext i j
  simp [cornerCompression, eigenbasisConj,
    KazhdanCornerMatrices.principalBlock,
    KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply]

theorem cornerCompression_add
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (C D : Matrix Z Z ℂ) :
    cornerCompression hP (C + D) =
      cornerCompression hP C + cornerCompression hP D := by
  ext i j
  simp [cornerCompression, eigenbasisConj, Matrix.mul_add, Matrix.add_mul,
    KazhdanCornerMatrices.principalBlock,
    KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply]

theorem cornerCompression_smul
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (c : ℂ) (C : Matrix Z Z ℂ) :
    cornerCompression hP (c • C) = c • cornerCompression hP C := by
  ext i j
  simp [cornerCompression, eigenbasisConj,
    KazhdanCornerMatrices.principalBlock,
    KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply]

theorem cornerCompression_conjTranspose
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (C : Matrix Z Z ℂ) :
    cornerCompression hP Cᴴ = (cornerCompression hP C)ᴴ := by
  rw [cornerCompression, cornerCompression,
    ← eigenbasisConj_conjTranspose,
    KazhdanCornerMatrices.principalBlock_conjTranspose]

/-- A projection becomes the identity of its range matrix algebra. -/
theorem cornerCompression_projection_eq_one
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P) :
    cornerCompression hP P = 1 := by
  rw [cornerCompression, eigenbasisConj_eq_coordinateProjection hP hPidem]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [KazhdanCornerMatrices.principalBlock,
      KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply,
      coordinateProjection, i.property]
  · have hval : (i : Z) ≠ (j : Z) := fun h ↦ hij (Subtype.ext h)
    simp [KazhdanCornerMatrices.principalBlock,
      KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply,
      coordinateProjection, hij, hval]

/-- Compression is multiplicative on two matrices which commute with the
projection. -/
theorem cornerCompression_mul_of_commute
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P B C : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P)
    (hB : B * P = P * B) (hC : C * P = P * C) :
    cornerCompression hP (B * C) =
      cornerCompression hP B * cornerCompression hP C := by
  have hle := norm_cornerCompression_mul_defect_le hP hPidem (B * C) B C
  have hzero :
      ‖cornerCompression hP (B * C) -
        cornerCompression hP B * cornerCompression hP C‖ = 0 := by
    apply le_antisymm
    · simpa [hB, hC] using hle
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- A two-sided compression by a projection commutes with that projection. -/
theorem projectionSandwich_commutes
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hPidem : P * P = P) (C : Matrix Z Z ℂ) :
    (P * C * P) * P = P * (P * C * P) := by
  calc
    (P * C * P) * P = P * C * (P * P) := by noncomm_ring
    _ = P * C * P := by rw [hPidem]
    _ = (P * P) * C * P := by rw [hPidem]
    _ = P * (P * C * P) := by noncomm_ring

/-- Consequently compression is exactly multiplicative on two projection
sandwiches. -/
theorem cornerCompression_projectionSandwich_mul
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P)
    (B C : Matrix Z Z ℂ) :
    cornerCompression hP ((P * B * P) * (P * C * P)) =
      cornerCompression hP (P * B * P) *
        cornerCompression hP (P * C * P) :=
  cornerCompression_mul_of_commute hP hPidem
    (projectionSandwich_commutes hPidem B)
    (projectionSandwich_commutes hPidem C)

/-- Compression to the range coordinates preserves the operator norm of a
projection sandwich. -/
theorem norm_cornerCompression_projectionSandwich
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P)
    (B : Matrix Z Z ℂ) :
    ‖cornerCompression hP (P * B * P)‖ = ‖P * B * P‖ := by
  have hembed := cornerEmbed_cornerCompression hP hPidem (P * B * P)
  have hsandwich : P * (P * B * P) * P = P * B * P := by
    calc
      P * (P * B * P) * P = (P * P) * B * (P * P) := by noncomm_ring
      _ = P * B * P := by rw [hPidem]
  calc
    ‖cornerCompression hP (P * B * P)‖ =
        ‖cornerEmbed hP (cornerCompression hP (P * B * P))‖ :=
      (norm_cornerEmbed hP _).symm
    _ = ‖P * (P * B * P) * P‖ :=
      congrArg (fun C : Matrix Z Z ℂ ↦ ‖C‖) hembed
    _ = ‖P * B * P‖ :=
      congrArg (fun C : Matrix Z Z ℂ ↦ ‖C‖) hsandwich

theorem cornerPredicate_iff_eigenvalue_ne_zero
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P) (i : Z) :
    cornerPredicate hP i ↔ hP.eigenvalues i ≠ 0 := by
  rcases eigenvalues_eq_zero_or_one hP hPidem i with hi | hi
  · simp [cornerPredicate, hi]
  · simp [cornerPredicate, hi]
    norm_num

/-- The coordinate type selected by the spectral projection has cardinality
equal to the matrix rank. -/
theorem card_cornerPredicate_eq_rank
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P) :
    Fintype.card {i : Z // cornerPredicate hP i} = P.rank := by
  let e : {i : Z // cornerPredicate hP i} ≃
      {i : Z // hP.eigenvalues i ≠ 0} :=
    { toFun := fun i ↦
        ⟨i, (cornerPredicate_iff_eigenvalue_ne_zero hP hPidem i).mp i.property⟩
      invFun := fun i ↦
        ⟨i, (cornerPredicate_iff_eigenvalue_ne_zero hP hPidem i).mpr i.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (Fintype.card_congr e).trans hP.rank_eq_card_non_zero_eigs.symm

/-- The projection at the `k`-th nonzero support coordinate. -/
def relabelledProjection
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    Matrix (Y (supportRelabelling Y P hne k))
      (Y (supportRelabelling Y P hne k)) ℂ :=
  P (supportRelabelling Y P hne k)

theorem relabelledProjection_isOrthogonalProjection
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    IsOrthogonalProjectionMatrix (relabelledProjection Y P hne k) :=
  hP _

theorem relabelledProjection_ne_zero
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    relabelledProjection Y P hne k ≠ 0 :=
  supportRelabelling_ne_zero Y P hne k

theorem relabelledProjection_rank_pos
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    0 < (relabelledProjection Y P hne k).rank :=
  CollapseDiscardCoordinates.rank_pos_of_ne_zero
    (relabelledProjection_isOrthogonalProjection Y P hP hne k)
    (relabelledProjection_ne_zero Y P hne k)

/-- The full matrix index type of the relabelled projection range. -/
abbrev relabelledCornerModel
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    FiniteModel :=
  ⟨{i : Y (supportRelabelling Y P hne k) //
      cornerPredicate
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1 i},
    inferInstance, inferInstance⟩

theorem card_relabelledCornerModel_eq_rank
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    Fintype.card (relabelledCornerModel Y P hP hne k) =
      (relabelledProjection Y P hne k).rank :=
  by
    change Fintype.card
        {i : Y (supportRelabelling Y P hne k) //
          cornerPredicate
            (relabelledProjection_isOrthogonalProjection Y P hP hne k).1 i} =
      (relabelledProjection Y P hne k).rank
    exact card_cornerPredicate_eq_rank
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).2

theorem card_relabelledCornerModel_pos
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    0 < Fintype.card (relabelledCornerModel Y P hP hne k) := by
  rw [card_relabelledCornerModel_eq_rank Y P hP hne k]
  exact relabelledProjection_rank_pos Y P hP hne k

theorem relabelledCornerModel_nonempty
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    Nonempty (relabelledCornerModel Y P hP hne k) :=
  Fintype.card_pos_iff.mp (card_relabelledCornerModel_pos Y P hP hne k)

noncomputable instance relabelledCornerModel.instNonempty
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) (k : ℕ) :
    Nonempty (relabelledCornerModel Y P hP hne k) :=
  relabelledCornerModel_nonempty Y P hP hne k

/-! ## Bounded coordinate compression -/

/-- Compress a bounded ambient family to the relabelled projection-range
matrix models.  Coordinate compression is contractive, so the resulting
family is uniformly bounded. -/
def cornerCompressSequence
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    BoundedMatrixSequence
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) :=
  ⟨fun k ↦ cornerCompression
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
      (x (supportRelabelling Y P hne k)),
    memℓp_infty ⟨‖x‖, by
      rintro _ ⟨k, rfl⟩
      exact (norm_cornerCompression_le
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        (x (supportRelabelling Y P hne k))).trans
          (boundedMatrixSequence_coord_norm_le (fun n ↦ Y n) x
            (supportRelabelling Y P hne k))⟩⟩

@[simp]
theorem cornerCompressSequence_apply
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) (k : ℕ) :
    (cornerCompressSequence Y P hP hne x k :
      Matrix (relabelledCornerModel Y P hP hne k)
        (relabelledCornerModel Y P hP hne k) ℂ) =
      cornerCompression
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        (x (supportRelabelling Y P hne k)) :=
  rfl

@[simp]
theorem cornerCompressSequence_zero
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    cornerCompressSequence Y P hP hne 0 = 0 := by
  refine lp.ext (funext fun k ↦ ?_)
  change cornerCompression
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1 0 = 0
  exact cornerCompression_zero _

/-- Coordinate compression, bundled as a complex linear map between the two
bounded-sequence spaces. -/
def cornerCompressSequenceLinear
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    BoundedMatrixSequence (fun n ↦ Y n) →ₗ[ℂ]
      BoundedMatrixSequence
        (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) where
  toFun := cornerCompressSequence Y P hP hne
  map_add' x y := by
    refine lp.ext (funext fun k ↦ ?_)
    change cornerCompression
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
          (x (supportRelabelling Y P hne k) +
            y (supportRelabelling Y P hne k)) =
      cornerCompression
          (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
          (x (supportRelabelling Y P hne k)) +
        cornerCompression
          (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
          (y (supportRelabelling Y P hne k))
    exact cornerCompression_add _ _ _
  map_smul' c x := by
    refine lp.ext (funext fun k ↦ ?_)
    change cornerCompression
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
          (c • x (supportRelabelling Y P hne k)) =
      c • cornerCompression
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        (x (supportRelabelling Y P hne k))
    exact cornerCompression_smul _ _ _

@[simp]
theorem cornerCompressSequenceLinear_apply
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerCompressSequenceLinear Y P hP hne x =
      cornerCompressSequence Y P hP hne x :=
  rfl

/-- Bounded coordinate compression respects adjoints exactly. -/
theorem cornerCompressSequence_star
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerCompressSequence Y P hP hne (star x) =
      star (cornerCompressSequence Y P hP hne x) := by
  refine lp.ext (funext fun k ↦ ?_)
  change cornerCompression
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        ((x (supportRelabelling Y P hne k) :
          Matrix (Y (supportRelabelling Y P hne k))
            (Y (supportRelabelling Y P hne k)) ℂ)ᴴ) =
    (cornerCompression
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
      (x (supportRelabelling Y P hne k)))ᴴ
  exact cornerCompression_conjTranspose _ _

/-- The projection lift compresses to the identity bounded sequence in its
range models. -/
theorem cornerCompressSequence_projection_eq_one
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    cornerCompressSequence Y P hP hne P = 1 := by
  refine lp.ext (funext fun k ↦ ?_)
  change cornerCompression
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
      (relabelledProjection Y P hne k) = 1
  exact cornerCompression_projection_eq_one
    (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
    (relabelledProjection_isOrthogonalProjection Y P hP hne k).2

/-- Bounded coordinate compression is exactly multiplicative on two families
which have first been sandwiched by the projection lift. -/
theorem cornerCompressSequence_projectionSandwich_mul
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x y : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerCompressSequence Y P hP hne ((P * x * P) * (P * y * P)) =
      cornerCompressSequence Y P hP hne (P * x * P) *
        cornerCompressSequence Y P hP hne (P * y * P) := by
  refine lp.ext (funext fun k ↦ ?_)
  change cornerCompression
      (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
      (((P (supportRelabelling Y P hne k) :
          Matrix (Y (supportRelabelling Y P hne k))
            (Y (supportRelabelling Y P hne k)) ℂ) *
        x (supportRelabelling Y P hne k) * P (supportRelabelling Y P hne k)) *
       ((P (supportRelabelling Y P hne k) :
          Matrix (Y (supportRelabelling Y P hne k))
            (Y (supportRelabelling Y P hne k)) ℂ) *
        y (supportRelabelling Y P hne k) * P (supportRelabelling Y P hne k))) =
    cornerCompression
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        ((P (supportRelabelling Y P hne k) :
          Matrix (Y (supportRelabelling Y P hne k))
            (Y (supportRelabelling Y P hne k)) ℂ) *
          x (supportRelabelling Y P hne k) * P (supportRelabelling Y P hne k)) *
      cornerCompression
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        ((P (supportRelabelling Y P hne k) :
          Matrix (Y (supportRelabelling Y P hne k))
            (Y (supportRelabelling Y P hne k)) ℂ) *
          y (supportRelabelling Y P hne k) * P (supportRelabelling Y P hne k))
  exact cornerCompression_projectionSandwich_mul
    (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
    (relabelledProjection_isOrthogonalProjection Y P hP hne k).2 _ _

/-- Coordinate compression carries ambient cofinite-null families to
cofinite-null corner families.  This is the well-definedness direction needed
for a later quotient map; the converse is a separate norm-reflection theorem
and is not asserted here. -/
theorem isNull_cornerCompressSequence
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n))
    (hx : IsNullMatrixSequence (fun n ↦ Y n) cofinite x) :
    IsNullMatrixSequence
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) cofinite
      (cornerCompressSequence Y P hP hne x) := by
  rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop] at hx ⊢
  apply squeeze_zero'
    (Eventually.of_forall fun k ↦
      norm_nonneg (cornerCompressSequence Y P hP hne x k))
  · exact Eventually.of_forall fun k ↦
      norm_cornerCompression_le
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        (x (supportRelabelling Y P hne k))
  · exact hx.comp (supportRelabelling_strictMono Y P hne).tendsto_atTop

/-- On projection-sandwiched families, coordinate compression preserves and
reflects cofinite nullity.  Reflection uses the full increasing enumeration
of every nonzero coordinate of `P`; an arbitrary subsequence would not
suffice. -/
theorem isNull_cornerCompressSequence_projectionSandwich_iff
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    IsNullMatrixSequence
        (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) cofinite
        (cornerCompressSequence Y P hP hne (P * x * P)) ↔
      IsNullMatrixSequence (fun n ↦ Y n) cofinite (P * x * P) := by
  constructor
  · intro hcorner
    have hnorm :
        (fun k ↦ ‖supportReindex Y P hne (P * x * P) k‖) =
          fun k ↦ ‖cornerCompressSequence Y P hP hne (P * x * P) k‖ := by
      funext k
      change
        ‖(P (supportRelabelling Y P hne k) :
              Matrix (Y (supportRelabelling Y P hne k))
                (Y (supportRelabelling Y P hne k)) ℂ) *
            x (supportRelabelling Y P hne k) *
            P (supportRelabelling Y P hne k)‖ =
          ‖cornerCompression
            (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
            ((P (supportRelabelling Y P hne k) :
                Matrix (Y (supportRelabelling Y P hne k))
                  (Y (supportRelabelling Y P hne k)) ℂ) *
              x (supportRelabelling Y P hne k) *
              P (supportRelabelling Y P hne k))‖
      exact (norm_cornerCompression_projectionSandwich
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).1
        (relabelledProjection_isOrthogonalProjection Y P hP hne k).2
        (x (supportRelabelling Y P hne k))).symm
    have hreindexed :
        IsNullMatrixSequence
          (fun k ↦ Y (supportRelabelling Y P hne k)) cofinite
          (supportReindex Y P hne (P * x * P)) := by
      rw [IsNullMatrixSequence] at hcorner ⊢
      rw [hnorm]
      exact hcorner
    exact (isNull_compressFamily_supportReindex_iff Y P x hne).mpr hreindexed
  · exact isNull_cornerCompressSequence Y P hP hne (P * x * P)

/-! ## The corner class of an ambient bounded family -/

/-- Compress a bounded family and then take its class in the relabelled
corner corona.  This is not asserted to be multiplicative on arbitrary
ambient families. -/
def cornerClass
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    NormMatrixCStarCorona
      (fun k ↦ (relabelledCornerModel Y P hP hne k : Type)) :=
  normMatrixCStarCoronaMk
    (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))
    (cornerCompressSequence Y P hP hne x)

/-- Ambient null families have zero corner class. -/
theorem cornerClass_eq_zero_of_isNull
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x : BoundedMatrixSequence (fun n ↦ Y n))
    (hx : IsNullMatrixSequence (fun n ↦ Y n) cofinite x) :
    cornerClass Y P hP hne x = 0 := by
  apply (normMatrixCStarCoronaMk_eq_zero_iff
    (fun k ↦ (relabelledCornerModel Y P hP hne k : Type))
    (cornerCompressSequence Y P hP hne x)).mpr
  exact isNull_cornerCompressSequence Y P hP hne x hx

/-- The projection lift represents the unit of the corner corona. -/
theorem cornerClass_projection_eq_one
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0) :
    cornerClass Y P hP hne P = 1 := by
  rw [cornerClass, cornerCompressSequence_projection_eq_one, map_one]

/-- The corner class is exactly multiplicative on projection-sandwiched
families. -/
theorem cornerClass_projectionSandwich_mul
    (P : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) P ≠ 0)
    (x y : BoundedMatrixSequence (fun n ↦ Y n)) :
    cornerClass Y P hP hne ((P * x * P) * (P * y * P)) =
      cornerClass Y P hP hne (P * x * P) *
        cornerClass Y P hP hne (P * y * P) := by
  rw [cornerClass, cornerClass, cornerClass,
    cornerCompressSequence_projectionSandwich_mul, map_mul]

/-- The image of the source unit, which is the unit of the represented
corner. -/
def supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    NormMatrixCStarCorona (fun n ↦ Y n) :=
  e 1

omit [Nontrivial A] in
/-- The support of a nonunital star homomorphism is self-adjoint. -/
theorem star_supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    star (supportProjection Y e) = supportProjection Y e := by
  rw [supportProjection, ← map_star]
  simp

omit [Nontrivial A] in
/-- The support of a nonunital star homomorphism is idempotent. -/
theorem supportProjection_mul_self
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    supportProjection Y e * supportProjection Y e = supportProjection Y e := by
  rw [supportProjection, ← map_mul]
  simp

/-- Injectivity prevents the support projection from vanishing. -/
theorem supportProjection_ne_zero
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (he : Function.Injective e) :
    supportProjection Y e ≠ 0 := by
  intro hzero
  have hmap : e (1 : A) = e 0 := by
    simpa [supportProjection] using hzero
  exact one_ne_zero (he hmap)

omit [Nontrivial A] in
/-- The support acts as a left identity on the represented algebra. -/
theorem supportProjection_mul_apply
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (a : A) :
    supportProjection Y e * e a = e a := by
  rw [supportProjection, ← map_mul, one_mul]

omit [Nontrivial A] in
/-- The support acts as a right identity on the represented algebra. -/
theorem apply_mul_supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (a : A) :
    e a * supportProjection Y e = e a := by
  rw [supportProjection, ← map_mul, mul_one]

/-- An injective nonunital corona representation has a projection lift of its
support with infinitely many nonzero coordinates. -/
theorem exists_projection_lift_with_infinite_support
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (he : Function.Injective e) :
    ∃ P : BoundedMatrixSequence (fun n ↦ Y n),
      (∀ n, IsOrthogonalProjectionMatrix (P n)) ∧
        normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e ∧
          {n : ℕ | (P n : Matrix (Y n) (Y n) ℂ) ≠ 0}.Infinite := by
  obtain ⟨P, hP, hPmk⟩ :=
    CollapseProjectionLift.exists_projection_lift Y (supportProjection Y e)
      (star_supportProjection Y e) (supportProjection_mul_self Y e)
  refine ⟨P, hP, hPmk, ?_⟩
  apply CollapseDiscardCoordinates.support_infinite_of_mk_ne_zero Y P
  rw [hPmk]
  exact supportProjection_ne_zero Y e he

omit [Nontrivial A] in
/-- Compressing any lift by a projection lift of the support does not change
the represented corona element.  Thus the represented algebra is literally
carried by the coordinate corners before those corners are relabelled and
identified with full matrix algebras. -/
theorem mk_compress_lift_eq
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (P x : BoundedMatrixSequence (fun n ↦ Y n))
    (hP : normMatrixCStarCoronaMk (fun n ↦ Y n) P = supportProjection Y e)
    (a : A) (hx : normMatrixCStarCoronaMk (fun n ↦ Y n) x = e a) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) (P * x * P) = e a := by
  rw [map_mul, map_mul, hP, hx, supportProjection_mul_apply,
    apply_mul_supportProjection]

#audit_axioms supportProjection_ne_zero
#audit_axioms exists_projection_lift_with_infinite_support
#audit_axioms mk_compress_lift_eq
#audit_axioms range_increasingEnumeration
#audit_axioms scalar_tendsto_zero_iff_increasingEnumeration
#audit_axioms isNull_reindex_iff_of_supported
#audit_axioms range_supportRelabelling
#audit_axioms supportRelabelling_surjective
#audit_axioms isNull_supportReindex_iff
#audit_axioms isNull_compressFamily_supportReindex_iff
#audit_axioms card_cornerPredicate_eq_rank
#audit_axioms card_relabelledCornerModel_eq_rank
#audit_axioms card_relabelledCornerModel_pos
#audit_axioms cornerCompressSequence_star
#audit_axioms cornerCompressSequence_projection_eq_one
#audit_axioms cornerCompressSequence_projectionSandwich_mul
#audit_axioms norm_cornerCompression_projectionSandwich
#audit_axioms isNull_cornerCompressSequence
#audit_axioms isNull_cornerCompressSequence_projectionSandwich_iff
#audit_axioms cornerClass_eq_zero_of_isNull
#audit_axioms cornerClass_projection_eq_one
#audit_axioms cornerClass_projectionSandwich_mul

end

end NonUnitalMFSupportCorner
end GroupApproximation
