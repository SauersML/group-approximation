import GroupApproximation.Analysis.VoiculescuPartition
import GroupApproximation.Analysis.VoiculescuBlockRecursion

/-!
# (V4, general) The superposition `W = Σⱼ Vⱼ dⱼ`

`Analysis/VoiculescuPartition` cuts the space; this module assembles the isometry
from the cut.  Given isometries `Vⱼ : K → H` with pairwise orthogonal ranges and
a partition `dⱼ`, the superposition is `Σⱼ Vⱼdⱼ`, and two facts about it are what
the reduction runs on.

## Where the orthogonality is spent

`adjoint_superposition_comp_self` is the identity

    `(Σⱼ Vⱼdⱼ)⋆(Σ_k V_k d_k) = Σ_{j,k} dⱼ (Vⱼ⋆V_k) d_k = Σⱼ dⱼ²` ,

the cross terms vanishing because `Vⱼ⋆V_k = 0` off the diagonal.  This is the
same orthogonality the block-diagonal case used to keep blocks apart, but here it
does more work: it is the whole reason the superposition is isometric, since the
partition's squares resolve the identity.

## The defect, and the two things it costs

`norm_superposition_defect_le` is the estimate the reduction is priced by, and it
comes from one exact identity,

    `S(Vⱼdⱼ) - (Vⱼdⱼ)R = (SVⱼ - VⱼR)dⱼ + Vⱼ(Rdⱼ - dⱼR)` ,

so the superposition's defect is bounded by the sum of the *per-piece* defects
plus the sum of the *commutators* of the partition with `R`.  The first is made
summable by running the intertwining step at a summable tolerance.  For the
second, bare quasicentrality is not enough: `‖[dⱼ,R]‖ → 0` does not imply that
`∑ⱼ ‖[dⱼ,R]‖` converges.  The construction must choose the monotone unit's
subsequence diagonally, before taking successive square roots, so these
commutators are summable on the dense target family.  This is why
`QuasicentralPartition.summable_comm` carries summability rather than merely a
limit-to-zero clause.

## A clause the datum did not have to record

`QuasicentralPartition.norm_le_one` derives `‖dⱼ‖ ≤ 1` from the datum rather than
asking for it: the partial sums of `Σⱼ ‖dⱼx‖²` are monotone and converge to
`‖x‖²`, so each is at most `‖x‖²`, so each single term is.  Worth noting because
the contraction bound is used twice in the estimate below and it would have been
natural — and wrong — to add it as a hypothesis.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {K H : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The pieces are contractions -/

/-- **The contraction bound is already in the datum.**  The partial sums of
`Σⱼ ‖dⱼx‖²` increase to `‖x‖²`, so no single term exceeds it. -/
theorem QuasicentralPartition.norm_le_one {S : ℕ → (K →L[ℂ] K)}
    (P : QuasicentralPartition K S) (j : ℕ) : ‖P.d j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul]
  have hmono : Monotone fun N ↦ ∑ i ∈ Finset.range N, ‖P.d i x‖ ^ 2 := by
    refine monotone_nat_of_le_succ fun N ↦ ?_
    rw [Finset.sum_range_succ]
    have : (0:ℝ) ≤ ‖P.d N x‖ ^ 2 := by positivity
    linarith
  have hle := hmono.ge_of_tendsto (P.tendsto_sum_norm_sq x) (j + 1)
  have hterm : ‖P.d j x‖ ^ 2 ≤ ∑ i ∈ Finset.range (j + 1), ‖P.d i x‖ ^ 2 := by
    refine Finset.single_le_sum (f := fun i ↦ ‖P.d i x‖ ^ 2) (fun i _ ↦ by positivity) ?_
    exact Finset.self_mem_range_succ j
  have hsq : ‖P.d j x‖ ^ 2 ≤ ‖x‖ ^ 2 := le_trans hterm hle
  nlinarith [norm_nonneg (P.d j x), norm_nonneg x]

/-! ## The superposition -/

variable (V : ℕ → (K →L[ℂ] H)) (d : ℕ → (K →L[ℂ] K))

/-- The partial superposition `Σ_{j<N} Vⱼ dⱼ`. -/
def superposition (N : ℕ) : K →L[ℂ] H :=
  ∑ j ∈ Finset.range N, V j ∘L d j

variable {V}

/-- Orthogonal ranges, in the form the Gram identity consumes. -/
theorem adjoint_comp_eq_zero_of_orthogonal
    (h : ∀ j k, j ≠ k → ∀ (x y : K), ⟪V j x, V k y⟫_ℂ = 0) {j k : ℕ}
    (hjk : j ≠ k) : ContinuousLinearMap.adjoint (V j) ∘L V k = 0 := by
  refine ContinuousLinearMap.ext fun y ↦ ?_
  refine ext_inner_left ℂ fun x ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    zero_apply, inner_zero_right]
  exact h j k hjk x y

/-- **The Gram identity: where the orthogonality is spent.** -/
theorem adjoint_superposition_comp_self
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    (hsa : ∀ j, IsSelfAdjoint (d j)) (N : ℕ) :
    ContinuousLinearMap.adjoint (superposition V d N) ∘L superposition V d N
      = ∑ j ∈ Finset.range N, d j * d j := by
  have hadj : ContinuousLinearMap.adjoint (superposition V d N)
      = ∑ j ∈ Finset.range N, d j ∘L ContinuousLinearMap.adjoint (V j) := by
    rw [superposition, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ContinuousLinearMap.adjoint_comp]
    congr 1
    exact (ContinuousLinearMap.star_eq_adjoint (d j)).symm.trans (hsa j).star_eq
  refine ContinuousLinearMap.ext fun x ↦ ?_
  have hinner : ∀ j ∈ Finset.range N,
      ContinuousLinearMap.adjoint (V j)
          (∑ k ∈ Finset.range N, V k (d k x)) = d j x := by
    intro j _
    rw [map_sum, Finset.sum_eq_single j]
    · have h := congrArg (fun T : K →L[ℂ] K ↦ T (d j x)) (hiso j)
      simpa using h
    · intro k _ hkj
      have h := congrArg (fun T : K →L[ℂ] K ↦ T (d k x)) (horth j k (Ne.symm hkj))
      simpa using h
    · intro h
      exact absurd (Finset.mem_range.mpr (Finset.mem_range.mp ‹j ∈ Finset.range N›)) h
  rw [ContinuousLinearMap.comp_apply, hadj]
  show (∑ j ∈ Finset.range N, d j ∘L ContinuousLinearMap.adjoint (V j))
      ((superposition V d N) x) = _
  rw [sum_apply, sum_apply]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [ContinuousLinearMap.comp_apply]
  have hx : (superposition V d N) x = ∑ k ∈ Finset.range N, V k (d k x) := by
    rw [superposition, sum_apply]
    exact Finset.sum_congr rfl fun k _ ↦ rfl
  rw [hx, hinner j hj]
  rfl

/-! ## The defect estimate -/

omit [CompleteSpace K] [CompleteSpace H] in
/-- The exact identity behind the estimate. -/
theorem superposition_defect_term (S : H →L[ℂ] H) (R : K →L[ℂ] K) (j : ℕ) :
    S ∘L (V j ∘L d j) - (V j ∘L d j) ∘L R
      = (S ∘L V j - V j ∘L R) ∘L d j + V j ∘L (R ∘L d j - d j ∘L R) := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, sub_apply,
    add_apply, map_sub]
  abel

/-- **The defect estimate.**  The superposition's defect is bounded by the
per-piece defects plus the commutators of the partition with `R`. -/
theorem norm_superposition_defect_le
    (hViso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (hd : ∀ j, ‖d j‖ ≤ 1) (S : H →L[ℂ] H) (R : K →L[ℂ] K) (N : ℕ) :
    ‖S ∘L superposition V d N - superposition V d N ∘L R‖
      ≤ (∑ j ∈ Finset.range N, ‖S ∘L V j - V j ∘L R‖)
        + ∑ j ∈ Finset.range N, ‖d j * R - R * d j‖ := by
  have hVnorm : ∀ j, ‖V j‖ ≤ 1 := by
    intro j
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    rw [one_mul]
    have hiso := (ContinuousLinearMap.isometry_iff_adjoint_comp_self (V j)).mpr
      (hViso j)
    exact le_of_eq (hiso.norm_map_of_map_zero (map_zero _) x)
  have hsplit : S ∘L superposition V d N - superposition V d N ∘L R
      = ∑ j ∈ Finset.range N,
        ((S ∘L V j - V j ∘L R) ∘L d j + V j ∘L (R ∘L d j - d j ∘L R)) := by
    rw [← Finset.sum_congr rfl fun j _ ↦ superposition_defect_term d S R j]
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [sum_apply]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, sub_apply]
    rw [superposition, sum_apply, sum_apply, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ rfl
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(S ∘L V j - V j ∘L R) ∘L d j‖ ≤ ‖S ∘L V j - V j ∘L R‖ := by
    refine le_trans ((S ∘L V j - V j ∘L R).opNorm_comp_le (d j)) ?_
    calc ‖S ∘L V j - V j ∘L R‖ * ‖d j‖ ≤ ‖S ∘L V j - V j ∘L R‖ * 1 :=
          mul_le_mul_of_nonneg_left (hd j) (norm_nonneg _)
      _ = ‖S ∘L V j - V j ∘L R‖ := mul_one _
  have h2 : ‖V j ∘L (R ∘L d j - d j ∘L R)‖ ≤ ‖d j * R - R * d j‖ := by
    refine le_trans ((V j).opNorm_comp_le _) ?_
    have hrw : ‖R ∘L d j - d j ∘L R‖ = ‖d j * R - R * d j‖ := by
      rw [← norm_neg]
      congr 1
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
      abel
    calc ‖V j‖ * ‖R ∘L d j - d j ∘L R‖ ≤ 1 * ‖R ∘L d j - d j ∘L R‖ :=
          mul_le_mul_of_nonneg_right (hVnorm j) (norm_nonneg _)
      _ = ‖R ∘L d j - d j ∘L R‖ := one_mul _
      _ = ‖d j * R - R * d j‖ := hrw
  linarith

end

end ShulmanFill
end GroupApproximation
