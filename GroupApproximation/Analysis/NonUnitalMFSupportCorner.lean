import GroupApproximation.Analysis.CollapseDiscardCoordinates
import GroupApproximation.Analysis.PrintedCornerCompression
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

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-! ## Increasing enumeration of an infinite subset of `ℕ` -/

/-- The least member of an infinite subset of `ℕ`. -/
noncomputable def leastMember (S : Set ℕ) (hS : S.Infinite) : ℕ :=
  Nat.find hS.nonempty

theorem leastMember_mem (S : Set ℕ) (hS : S.Infinite) :
    leastMember S hS ∈ S :=
  Nat.find_spec hS.nonempty

theorem leastMember_le (S : Set ℕ) (hS : S.Infinite)
    {n : ℕ} (hn : n ∈ S) : leastMember S hS ≤ n :=
  Nat.find_min' hS.nonempty hn

/-- The least member of `S` strictly above `n`. -/
noncomputable def nextMember (S : Set ℕ) (hS : S.Infinite) (n : ℕ) : ℕ :=
  Nat.find (Set.Infinite.exists_gt hS n)

theorem nextMember_mem (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    nextMember S hS n ∈ S :=
  (Nat.find_spec (Set.Infinite.exists_gt hS n)).1

theorem lt_nextMember (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    n < nextMember S hS n :=
  (Nat.find_spec (Set.Infinite.exists_gt hS n)).2

theorem nextMember_le (S : Set ℕ) (hS : S.Infinite) {n k : ℕ}
    (hk : k ∈ S) (hnk : n < k) : nextMember S hS n ≤ k :=
  Nat.find_min' (Set.Infinite.exists_gt hS n) ⟨hk, hnk⟩

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
  apply Set.Subset.antisymm
  · rintro _ ⟨n, rfl⟩
    exact increasingEnumeration_mem S hS n
  · intro k hk
    let f : ℕ → ℕ := increasingEnumeration S hS
    have hfmono : StrictMono f := increasingEnumeration_strictMono S hS
    have hex : ∃ n, k ≤ f n := ⟨k, hfmono.id_le k⟩
    refine ⟨Nat.find hex, ?_⟩
    apply le_antisymm ?_ (Nat.find_spec hex)
    generalize hN : Nat.find hex = N
    cases N with
    | zero =>
        rw [hN, increasingEnumeration_zero]
        exact leastMember_le S hS hk
    | succ n =>
        have hminimal : ¬ k ≤ f n := Nat.find_min hex (by omega)
        have hnlt : f n < k := Nat.lt_of_not_ge hminimal
        rw [hN, increasingEnumeration_succ]
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
    exact boundedMatrixSequence_coord_norm_le (fun n ↦ Y n) x (φ k)⟩⟩

@[simp]
theorem reindexBoundedMatrixSequence_apply (φ : ℕ → ℕ)
    (x : BoundedMatrixSequence (fun n ↦ Y n)) (k : ℕ) :
    (reindexBoundedMatrixSequence Y φ x k : Matrix (Y (φ k)) (Y (φ k)) ℂ) =
      x (φ k) :=
  rfl

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
        (Y (supportRelabelling Y P hne k)) ℂ) ≠ 0 :=
  increasingEnumeration_mem _ _ k

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

theorem cornerPredicate_iff_eigenvalue_ne_zero
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : P.IsHermitian) (hPidem : P * P = P) (i : Z) :
    cornerPredicate hP i ↔ hP.eigenvalues i ≠ 0 := by
  rcases eigenvalues_eq_zero_or_one hP hPidem i with hi | hi
  · simp [cornerPredicate, hi]
  · simp [cornerPredicate, hi]

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
  card_cornerPredicate_eq_rank
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

/-- The image of the source unit, which is the unit of the represented
corner. -/
def supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    NormMatrixCStarCorona (fun n ↦ Y n) :=
  e 1

/-- The support of a nonunital star homomorphism is self-adjoint. -/
theorem star_supportProjection
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)) :
    star (supportProjection Y e) = supportProjection Y e := by
  rw [supportProjection, ← map_star]
  simp

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

/-- The support acts as a left identity on the represented algebra. -/
theorem supportProjection_mul_apply
    (e : A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
    (a : A) :
    supportProjection Y e * e a = e a := by
  rw [supportProjection, ← map_mul, one_mul]

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

end

end NonUnitalMFSupportCorner
end GroupApproximation
