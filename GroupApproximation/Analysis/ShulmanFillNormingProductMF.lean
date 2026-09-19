import GroupApproximation.Analysis.ShulmanFillNormingPrefixBlock

/-!
# A bounded product of matrix algebras is MF-embeddable

`(xₙ)ₙ ↦ [j ↦ diag(x₀, …, x_j)]` is a `*`-homomorphism of the bounded product
`∏ₙ M_{Yₙ}` into the norm-matrix corona over the prefix block sums, and it is
faithful: the norm of a prefix block diagonal dominates each of its entries, so
a class that is null along the cofinite filter has every entry of norm zero.

No representative is chosen anywhere, which is why the map is multiplicative on
the nose.  That is special to *matrix* coordinate algebras: for general MF
coordinate algebras the entries would be corona classes, each with its own null
condition, and the block diagonal of chosen representatives would only be
well defined if the choices were null *uniformly in the coordinate*, which they
are not.  So this lemma is the printed case, not a general product permanence
statement, and the general one is not elementary.

It supplies `HasMFEmbedding 𝒟` — hence the MF endpoint of
`Analysis/ShulmanFillNormingGluing` — whenever the models of the `𝒟`
construction are the printed ones, `A n = M_{kₙ}`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

open scoped Matrix.Norms.L2Operator

noncomputable section

section ProductMF

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

-- Parameterised exactly as
-- `ReducedProductMFPermanence.boundedMatrixSequenceCStarAlgebraForReducedProductPermanence`:
-- fixing the family before the parents are assembled sends `StarModule`
-- synthesis into a heartbeat timeout.
noncomputable local instance boundedMatrixSequenceCStarAlgebraForProductMF
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The prefix models are nonempty, as an instance: `NormMatrixCStarCorona`
over them is only well-formed once instance search can see it. -/
instance nonemptyPrefixModelInstance (j : ℕ) : Nonempty (prefixModel Y j) :=
  nonempty_prefixModel Y inferInstance j

/-! ## Norms of prefix block diagonals -/

omit [∀ n, Nonempty (Y n)] in
/-- A uniform bound on the entries bounds every prefix block diagonal. -/
theorem norm_prefixDiag_le (x : ∀ n, Matrix (Y n) (Y n) ℂ) {C : ℝ}
    (hC : ∀ n, ‖x n‖ ≤ C) : ∀ j, ‖prefixDiag Y x j‖ ≤ C
  | 0 => hC 0
  | j + 1 => by
    show ‖blockDiagMatrix (prefixModel Y j) (Y (j + 1))
      (prefixDiag Y x j) (x (j + 1))‖ ≤ C
    rw [l2_opNorm_blockDiag]
    exact max_le (norm_prefixDiag_le x hC j) (hC (j + 1))

omit [∀ n, Nonempty (Y n)] in
/-- Each entry of index at most `j` is dominated by the `j`-th prefix block
diagonal.  This is what makes the embedding faithful. -/
theorem norm_le_norm_prefixDiag (x : ∀ n, Matrix (Y n) (Y n) ℂ) :
    ∀ (j n : ℕ), n ≤ j → ‖x n‖ ≤ ‖prefixDiag Y x j‖
  | 0, n, hn => by
    rw [Nat.le_zero.mp hn]
    exact le_rfl
  | j + 1, n, hn => by
    show ‖x n‖ ≤ ‖blockDiagMatrix (prefixModel Y j) (Y (j + 1))
      (prefixDiag Y x j) (x (j + 1))‖
    rw [l2_opNorm_blockDiag]
    rcases eq_or_lt_of_le hn with h | h
    · rw [h]
      exact le_max_right _ _
    · exact (norm_le_norm_prefixDiag x j n (Nat.lt_succ_iff.mp h)).trans
        (le_max_left _ _)

/-! ## The embedding -/

/-- The prefix block diagonal of a bounded matrix sequence, again bounded. -/
def prefixSeq (x : BoundedMatrixSequence (fun n ↦ Y n)) :
    BoundedMatrixSequence (fun j ↦ prefixModel Y j) :=
  ⟨fun j ↦ prefixDiag Y (fun n ↦ x n) j, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨j, rfl⟩
    exact norm_prefixDiag_le Y (fun n ↦ x n)
      (fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero x n) j⟩⟩

omit [∀ n, Nonempty (Y n)] in
@[simp] theorem prefixSeq_apply (x : BoundedMatrixSequence (fun n ↦ Y n))
    (j : ℕ) : prefixSeq Y x j = prefixDiag Y (fun n ↦ x n) j := rfl

/-- **Prefix block diagonalization is a `*`-homomorphism.**  Every clause is
the corresponding law of `prefixDiag`, read coordinatewise. -/
def prefixSeqHom :
    BoundedMatrixSequence (fun n ↦ Y n) →⋆ₙₐ[ℂ]
      BoundedMatrixSequence (fun j ↦ prefixModel Y j) where
  toFun := prefixSeq Y
  map_zero' := by
    apply lp.ext
    funext j
    exact prefixDiag_zero Y j
  map_add' x y := by
    apply lp.ext
    funext j
    exact prefixDiag_add Y (fun n ↦ x n) (fun n ↦ y n) j
  map_mul' x y := by
    apply lp.ext
    funext j
    exact prefixDiag_mul Y (fun n ↦ x n) (fun n ↦ y n) j
  map_smul' z x := by
    apply lp.ext
    funext j
    exact prefixDiag_smul Y (fun n ↦ x n) z j
  map_star' x := by
    apply lp.ext
    funext j
    exact prefixDiag_star Y (fun n ↦ x n) j

/-- The induced map into the norm-matrix corona over the prefix models. -/
def prefixCoronaHom :
    BoundedMatrixSequence (fun n ↦ Y n) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun j ↦ prefixModel Y j) :=
  (normMatrixCStarCoronaQuotient
    (fun j ↦ prefixModel Y j)).toNonUnitalStarAlgHom.comp (prefixSeqHom Y)

/-- **The embedding is faithful.**  If the prefix block diagonals of `x - y`
are null then, since each entry is dominated by every later prefix diagonal,
every entry of `x - y` has norm zero. -/
theorem prefixCoronaHom_injective :
    Function.Injective (prefixCoronaHom Y) := by
  intro x y hxy
  have hzero : prefixCoronaHom Y (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnull : IsNullMatrixSequence (fun j ↦ prefixModel Y j) cofinite
      (prefixSeq Y (x - y)) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun j ↦ prefixModel Y j) _).mp hzero
  have htend : Tendsto (fun j ↦ ‖prefixDiag Y (fun n ↦ (x - y) n) j‖)
      atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact hnull
  apply lp.ext
  funext n
  have hle : ‖x n - y n‖ ≤ 0 := by
    refine ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop n] with j hj
    exact norm_le_norm_prefixDiag Y (fun m ↦ (x - y) m) j n hj
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

/-- **A bounded product of matrix algebras is MF-embeddable.**  The prefix
block diagonals give a faithful `*`-homomorphism into one norm-matrix corona,
and `MFAlgebraDimension.hasMFEmbedding_iff` removes the monotonicity
requirement on the model sizes. -/
theorem hasMFEmbedding_boundedMatrixSequence :
    HasMFEmbedding (BoundedMatrixSequence (fun n ↦ Y n)) := by
  refine (MFAlgebraDimension.hasMFEmbedding_iff _).2 ?_
  refine ⟨fun j ↦ prefixModel Y j, nonempty_prefixModel Y inferInstance, ?_⟩
  exact ⟨card_prefixModel_pos Y inferInstance, prefixCoronaHom Y,
    prefixCoronaHom_injective Y⟩

end ProductMF

end

end ShulmanFill
end GroupApproximation
