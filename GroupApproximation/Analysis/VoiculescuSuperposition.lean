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

/-- **The finite Pythagorean identity for the partial superposition.**

This is the scalar form of `adjoint_superposition_comp_self` which the strong
limit construction consumes.  It is important that the right side is the
partition's actual finite square sum: no passage to an infinite operator sum
has happened yet. -/
theorem norm_superposition_apply_sq (P : QuasicentralPartition K d)
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    (N : ℕ) (x : K) :
    ‖superposition V P.d N x‖ ^ 2 =
      ∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2 := by
  have hgram := adjoint_superposition_comp_self (d := P.d) hiso horth
    P.isSelfAdjoint N
  have happ := congrArg (fun T : K →L[ℂ] K ↦ T x) hgram
  have hinner := congrArg (fun y : K ↦ ⟪x, y⟫_ℂ) happ
  have hleft :
      ⟪x, (ContinuousLinearMap.adjoint (superposition V P.d N) ∘L
        superposition V P.d N) x⟫_ℂ =
        (((‖superposition V P.d N x‖ ^ 2 : ℝ) : ℂ)) := by
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hright :
      ⟪x, (∑ j ∈ Finset.range N, P.d j * P.d j) x⟫_ℂ =
        (((∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2 : ℝ) : ℂ)) := by
    rw [sum_apply, inner_sum]
    push_cast
    exact Finset.sum_congr rfl fun j _ ↦ P.inner_sq j x
  rw [hleft, hright] at hinner
  exact_mod_cast hinner

/-- Every partial superposition is a contraction. -/
theorem norm_superposition_apply_le (P : QuasicentralPartition K d)
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    (N : ℕ) (x : K) : ‖superposition V P.d N x‖ ≤ ‖x‖ := by
  have hmono : Monotone fun M ↦ ∑ j ∈ Finset.range M, ‖P.d j x‖ ^ 2 := by
    refine monotone_nat_of_le_succ fun M ↦ ?_
    rw [Finset.sum_range_succ]
    positivity
  have hsqle := hmono.ge_of_tendsto (P.tendsto_sum_norm_sq x) N
  rw [norm_superposition_apply_sq P hiso horth N x] at hsqle
  nlinarith [norm_nonneg (superposition V P.d N x), norm_nonneg x]

/-- The operator norms of all partial superpositions are uniformly bounded by
one. -/
theorem norm_superposition_le_one (P : QuasicentralPartition K d)
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    (N : ℕ) : ‖superposition V P.d N‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  simpa using norm_superposition_apply_le P hiso horth N x

/-! ## The strong limit -/

/-- A partial superposition is orthogonal to every summand whose index is past
the end of the partial sum. -/
theorem inner_superposition_apply_eq_zero_of_le
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    {N j : ℕ} (hNj : N ≤ j) (x y : K) :
    ⟪superposition V d N x, V j y⟫_ℂ = 0 := by
  rw [superposition, sum_apply, sum_inner]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hij : i ≠ j :=
    ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hNj)
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.comp_apply, horth i j hij, zero_apply,
    inner_zero_right]

/-- **Finite-interval Pythagoras.**  The square norm of a tail of the
superposition is exactly the corresponding tail of the partition's square
sum. -/
theorem norm_superposition_sub_apply_sq (P : QuasicentralPartition K d)
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    {N M : ℕ} (hNM : N ≤ M) (x : K) :
    ‖superposition V P.d M x - superposition V P.d N x‖ ^ 2 =
      (∑ j ∈ Finset.range M, ‖P.d j x‖ ^ 2) -
        ∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2 := by
  induction M with
  | zero =>
      have hN : N = 0 := Nat.eq_zero_of_le_zero hNM
      subst N
      simp
  | succ M ih =>
      by_cases hN : N = M + 1
      · subst N
        simp
      · have hNM' : N ≤ M := by omega
        have hsucc :
            superposition V P.d (M + 1) x =
              superposition V P.d M x + V M (P.d M x) := by
          simp [superposition, Finset.sum_range_succ]
        have horthM :
            ⟪superposition V P.d M x, V M (P.d M x)⟫_ℂ = 0 :=
          inner_superposition_apply_eq_zero_of_le (d := P.d) horth
            (le_refl M) x (P.d M x)
        have horthN :
            ⟪superposition V P.d N x, V M (P.d M x)⟫_ℂ = 0 :=
          inner_superposition_apply_eq_zero_of_le (d := P.d) horth hNM'
            x (P.d M x)
        have htailOrth :
            ⟪superposition V P.d M x - superposition V P.d N x,
              V M (P.d M x)⟫_ℂ = 0 := by
          rw [inner_sub_left, horthM, horthN, sub_self]
        have hVnorm : ‖V M (P.d M x)‖ = ‖P.d M x‖ := by
          have hV : Isometry (V M) :=
            (ContinuousLinearMap.isometry_iff_adjoint_comp_self (V M)).mpr
              (hiso M)
          exact hV.norm_map_of_map_zero (map_zero _) _
        rw [hsucc]
        have hsplit :
            (superposition V P.d M x + V M (P.d M x)) -
                superposition V P.d N x =
              (superposition V P.d M x - superposition V P.d N x) +
                V M (P.d M x) := by
          abel
        rw [hsplit]
        calc
          ‖(superposition V P.d M x - superposition V P.d N x) +
              V M (P.d M x)‖ ^ 2 =
              ‖superposition V P.d M x - superposition V P.d N x‖ ^ 2 +
                ‖V M (P.d M x)‖ ^ 2 := by
            simpa [pow_two] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                (superposition V P.d M x - superposition V P.d N x)
                (V M (P.d M x)) htailOrth
          _ = (∑ j ∈ Finset.range (M + 1), ‖P.d j x‖ ^ 2) -
                ∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2 := by
            rw [ih hNM', hVnorm, Finset.sum_range_succ]
            ring

/-- The partial superpositions are pointwise Cauchy.  This is the exact
Hilbert-series step: finite-interval Pythagoras turns convergence of the
partition's scalar square sums into convergence of the vector series. -/
theorem cauchySeq_superposition (P : QuasicentralPartition K d)
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0)
    (x : K) : CauchySeq fun N ↦ superposition V P.d N x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let q : ℕ → ℝ := fun N ↦ ∑ j ∈ Finset.range N, ‖P.d j x‖ ^ 2
  have hqmono : Monotone q := by
    refine monotone_nat_of_le_succ fun N ↦ ?_
    dsimp [q]
    rw [Finset.sum_range_succ]
    positivity
  have hqtend : Tendsto q atTop (𝓝 (‖x‖ ^ 2)) := P.tendsto_sum_norm_sq x
  have hqle : ∀ N, q N ≤ ‖x‖ ^ 2 := fun N ↦ hqmono.ge_of_tendsto hqtend N
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hqtend) (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have htail : ∀ a b, N ≤ a → a ≤ b →
      dist (superposition V P.d b x) (superposition V P.d a x) < ε := by
    intro a b ha hab
    have hnear : dist (q a) (‖x‖ ^ 2) < ε ^ 2 := hN a ha
    have htailSq := norm_superposition_sub_apply_sq P hiso horth hab x
    have hqba : q b - q a < ε ^ 2 := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hqle a))] at hnear
      linarith [hqle b]
    rw [dist_eq_norm]
    change ‖superposition V P.d b x - superposition V P.d a x‖ < ε
    change ‖superposition V P.d b x - superposition V P.d a x‖ ^ 2 =
      q b - q a at htailSq
    nlinarith [norm_nonneg
      (superposition V P.d b x - superposition V P.d a x)]
  rcases le_total n m with hnm | hmn
  · exact htail n m hn hnm
  · rw [dist_comm]
    exact htail m n hm hmn

/-- **The superposition has an isometric strong limit.**

The finite Gram identities do all the operator-theoretic work: they uniformly
bound the partial maps and identify the norm of their limit with the partition
sum.  Finite-interval Pythagoras supplies pointwise Cauchy-ness, so no
infinite-series assumption remains. -/
theorem exists_isometric_superposition_limit
    (P : QuasicentralPartition K d)
    (hiso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (horth : ∀ j k, j ≠ k → ContinuousLinearMap.adjoint (V j) ∘L V k = 0) :
    ∃ W : K →L[ℂ] H,
      (∀ x : K, Tendsto (fun N ↦ superposition V P.d N x) atTop (𝓝 (W x))) ∧
      ContinuousLinearMap.adjoint W ∘L W = 1 := by
  classical
  have hcauchy : ∀ x : K, CauchySeq fun N ↦ superposition V P.d N x :=
    fun x ↦ cauchySeq_superposition P hiso horth x
  let f : K → H := fun x ↦
    Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x))
  have hf : ∀ x : K,
      Tendsto (fun N ↦ superposition V P.d N x) atTop (𝓝 (f x)) :=
    fun x ↦ Classical.choose_spec (cauchySeq_tendsto_of_complete (hcauchy x))
  have hadd : ∀ x y : K, f (x + y) = f x + f y := by
    intro x y
    refine tendsto_nhds_unique (hf (x + y)) ?_
    simpa only [map_add] using (hf x).add (hf y)
  have hsmul : ∀ (c : ℂ) (x : K), f (c • x) = c • f x := by
    intro c x
    refine tendsto_nhds_unique (hf (c • x)) ?_
    simpa only [map_smul] using (hf x).const_smul c
  have hbound : ∀ x : K, ‖f x‖ ≤ 1 * ‖x‖ := by
    intro x
    refine le_of_tendsto (hf x).norm (Eventually.of_forall fun N ↦ ?_)
    simpa using norm_superposition_apply_le P hiso horth N x
  let W : K →L[ℂ] H := LinearMap.mkContinuous
    { toFun := f
      map_add' := hadd
      map_smul' := hsmul }
    1 hbound
  have hW : ∀ x : K,
      Tendsto (fun N ↦ superposition V P.d N x) atTop (𝓝 (W x)) := by
    intro x
    exact hf x
  have hWnorm : ∀ x : K, ‖W x‖ = ‖x‖ := by
    intro x
    have hsquare : Tendsto (fun N ↦ ‖superposition V P.d N x‖ ^ 2)
        atTop (𝓝 (‖W x‖ ^ 2)) := (hW x).norm.pow 2
    have hsquare' : Tendsto (fun N ↦ ‖superposition V P.d N x‖ ^ 2)
        atTop (𝓝 (‖x‖ ^ 2)) :=
      (P.tendsto_sum_norm_sq x).congr fun N ↦
        (norm_superposition_apply_sq P hiso horth N x).symm
    have heq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := tendsto_nhds_unique hsquare hsquare'
    nlinarith [norm_nonneg (W x), norm_nonneg x]
  have hWiso : Isometry W :=
    (AddMonoidHomClass.isometry_iff_norm W).mpr hWnorm
  exact ⟨W, hW,
    (ContinuousLinearMap.isometry_iff_adjoint_comp_self W).mp hWiso⟩

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

omit [CompleteSpace K] [CompleteSpace H] in
/-- The defect of a finite superposition is the finite sum of its one-piece
defects. -/
theorem superposition_defect_eq_sum (S : H →L[ℂ] H) (R : K →L[ℂ] K)
    (N : ℕ) :
    S ∘L superposition V d N - superposition V d N ∘L R =
      ∑ j ∈ Finset.range N,
        ((S ∘L V j - V j ∘L R) ∘L d j +
          V j ∘L (R ∘L d j - d j ∘L R)) := by
  rw [← Finset.sum_congr rfl fun j _ ↦ superposition_defect_term d S R j]
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [sum_apply]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, sub_apply]
  rw [superposition, sum_apply, sum_apply, map_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ rfl

/-- The norm of a one-piece defect is bounded by its intertwining error and
its commutator error. -/
theorem norm_superposition_defect_term_le
    (hViso : ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (hd : ‖d j‖ ≤ 1) (S : H →L[ℂ] H) (R : K →L[ℂ] K) :
    ‖(S ∘L V j - V j ∘L R) ∘L d j +
        V j ∘L (R ∘L d j - d j ∘L R)‖
      ≤ ‖S ∘L V j - V j ∘L R‖ + ‖d j * R - R * d j‖ := by
  have hVnorm : ‖V j‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    rw [one_mul]
    have hiso :=
      (ContinuousLinearMap.isometry_iff_adjoint_comp_self (V j)).mpr hViso
    exact le_of_eq (hiso.norm_map_of_map_zero (map_zero _) x)
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(S ∘L V j - V j ∘L R) ∘L d j‖
      ≤ ‖S ∘L V j - V j ∘L R‖ := by
    refine le_trans ((S ∘L V j - V j ∘L R).opNorm_comp_le (d j)) ?_
    calc
      ‖S ∘L V j - V j ∘L R‖ * ‖d j‖
          ≤ ‖S ∘L V j - V j ∘L R‖ * 1 :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ = ‖S ∘L V j - V j ∘L R‖ := mul_one _
  have h2 : ‖V j ∘L (R ∘L d j - d j ∘L R)‖
      ≤ ‖d j * R - R * d j‖ := by
    refine le_trans ((V j).opNorm_comp_le _) ?_
    have hrw : ‖R ∘L d j - d j ∘L R‖ = ‖d j * R - R * d j‖ := by
      rw [← norm_neg]
      congr 1
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
      abel
    calc
      ‖V j‖ * ‖R ∘L d j - d j ∘L R‖
          ≤ 1 * ‖R ∘L d j - d j ∘L R‖ :=
        mul_le_mul_of_nonneg_right hVnorm (norm_nonneg _)
      _ = ‖R ∘L d j - d j ∘L R‖ := one_mul _
      _ = ‖d j * R - R * d j‖ := hrw
  linarith

/-- **The defect estimate.**  The superposition's defect is bounded by the
per-piece defects plus the commutators of the partition with `R`. -/
theorem norm_superposition_defect_le
    (hViso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (hd : ∀ j, ‖d j‖ ≤ 1) (S : H →L[ℂ] H) (R : K →L[ℂ] K) (N : ℕ) :
    ‖S ∘L superposition V d N - superposition V d N ∘L R‖
      ≤ (∑ j ∈ Finset.range N, ‖S ∘L V j - V j ∘L R‖)
        + ∑ j ∈ Finset.range N, ‖d j * R - R * d j‖ := by
  rw [superposition_defect_eq_sum]
  refine le_trans (norm_sum_le _ _) ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  exact norm_superposition_defect_term_le (hViso j) (hd j) S R

/-- **The partial defects converge in operator norm.**  The limit here is
written as the sum of the one-piece defects.  Identifying it with the defect of
the strong superposition limit is a separate continuity argument; the norm
convergence itself uses exactly the two summability inputs of the construction. -/
theorem tendsto_superposition_defect
    (hViso : ∀ j, ContinuousLinearMap.adjoint (V j) ∘L V j = 1)
    (hd : ∀ j, ‖d j‖ ≤ 1) (S : H →L[ℂ] H) (R : K →L[ℂ] K)
    (hpiece : Summable fun j ↦ ‖S ∘L V j - V j ∘L R‖)
    (hcomm : Summable fun j ↦ ‖d j * R - R * d j‖) :
    Tendsto
      (fun N ↦ S ∘L superposition V d N - superposition V d N ∘L R)
      atTop
      (𝓝 (∑' j, (S ∘L V j - V j ∘L R) ∘L d j +
        V j ∘L (R ∘L d j - d j ∘L R))) := by
  have hmajorant : Summable fun j ↦
      ‖S ∘L V j - V j ∘L R‖ + ‖d j * R - R * d j‖ :=
    hpiece.add hcomm
  have hsum : Summable fun j ↦
      (S ∘L V j - V j ∘L R) ∘L d j +
        V j ∘L (R ∘L d j - d j ∘L R) :=
    Summable.of_norm_bounded hmajorant fun j ↦
      norm_superposition_defect_term_le (hViso j) (hd j) S R
  simpa only [superposition_defect_eq_sum] using hsum.hasSum.tendsto_sum_nat

end

end ShulmanFill
end GroupApproximation
