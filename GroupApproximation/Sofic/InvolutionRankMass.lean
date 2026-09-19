import GroupApproximation.Sofic.ScaledKazhdanTransport

/-!
# The rank–mass calculus of a commuting pair of involutions

The scaled transport theory of `Sofic.ScaledKazhdanTransport` measures matrices
by their unnormalized Frobenius mass `matMass`, and is calibrated against an
arbitrary weight sequence.  For the analytic collapse argument the weight of
interest is a *rank* scale, so the mass and the rank of the relevant
displacements have to be compared exactly, not just up to a dimension factor.

The conceptual separation of the three metrics — operator norm for the
algebraic and covariance control, rank for the discrete support that survives
normalization, Hilbert--Schmidt for the energy property `(T)` acts on — was
prompted by a question of Francesco Fournier-Facio.

This file supplies that comparison for the involution (`m = 2`) case.  For two
commuting *exact involutions* — self-adjoint matrices squaring to `1` — the
displacement `T := u - w` is self-adjoint and satisfies `T³ = 4 T`, so
`T² / 4` is an orthogonal projection, the *half-square projection* of the pair.
The four facts proved here are:

* `matMass_sub_eq_four_mul_rank`: the Frobenius mass of `u - w` is exactly four
  times the rank of the half-square projection, so mass and rank are the *same*
  invariant on this locus, with no inequality lost;
* `rank_sub_le_add`: matrix rank obeys the triangle inequality along
  differences, so the rank displacement really is a metric;
* `rank_eq_of_projections_close`: orthogonal projections at operator distance
  less than `1` have equal rank, the rigidity that turns an approximate
  statement about projections into an exact statement about ranks;
* `matMass_le_rank_mul_sq_opNorm`: for an arbitrary matrix the Frobenius mass is
  at most `rank · ‖·‖²`, the reverse comparison, proved by summing the
  eigenvalues of the Gram matrix over the eigenbasis.

Together these say that on commuting involutions the rank displacement and the
Frobenius mass are interchangeable up to the explicit factor `4`, which is what
makes a mass-calibrated transport statement into a rank-calibrated one.
-/

namespace GroupApproximation
namespace InvolutionRankMass

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

/-! ## Frobenius mass as a Gram trace -/

/-- The unnormalized Frobenius mass of a matrix is the real part of the trace of
its Gram matrix. -/
theorem matMass_eq_re_trace_conjTranspose_mul {Y : Type*} [Fintype Y]
    (X : Matrix Y Y ℂ) :
    ScaledKazhdanTransport.matMass X = ((Xᴴ * X).trace).re := by
  have hdiag : ∀ j : Y,
      ∑ i : Y, Complex.normSq (X i j) = ((Xᴴ * X) j j).re := by
    intro j
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.conjTranspose_apply]
    calc
      Complex.normSq (X i j) = ((Complex.normSq (X i j) : ℝ) : ℂ).re := by simp
      _ = (star (X i j) * X i j).re :=
        congrArg Complex.re Complex.normSq_eq_conj_mul_self
  have hre : ((Xᴴ * X).trace).re = ∑ j : Y, ((Xᴴ * X) j j).re := by
    show (∑ j : Y, (Xᴴ * X) j j).re = _
    rw [Complex.re_sum]
  rw [hre]
  calc
    ScaledKazhdanTransport.matMass X
        = ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := rfl
    _ = ∑ j : Y, ∑ i : Y, Complex.normSq (X i j) := Finset.sum_comm
    _ = ∑ j : Y, ((Xᴴ * X) j j).re := Finset.sum_congr rfl fun j _ ↦ hdiag j

/-! ## Rank as a metric -/

/-- Matrix rank is subadditive: the range of a sum lies in the join of the two
ranges. -/
theorem rank_add_le {Y : Type*} [Fintype Y] (A B : Matrix Y Y ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rw [Matrix.mulVecLin_add]
    exact LinearMap.range_add_le _ _
  calc
    (A + B).rank ≤ Module.finrank ℂ
        ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
      Submodule.finrank_mono hle
    _ ≤ A.rank + B.rank := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- **Rank triangle inequality.**  The rank of a difference is a pseudometric on
square matrices. -/
theorem rank_sub_le_add {Y : Type*} [Fintype Y] (a b c : Matrix Y Y ℂ) :
    (a - c).rank ≤ (a - b).rank + (b - c).rank := by
  have hsplit : a - c = (a - b) + (b - c) := by abel
  rw [hsplit]
  exact rank_add_le _ _

/-! ## Trace and rank of an orthogonal projection -/

/-- The trace of an orthogonal projection matrix is its rank.  The matrix is
idempotent, hence a projection onto its own range, and the trace of a projection
endomorphism is the dimension of that range. -/
theorem re_trace_eq_rank_of_isOrthogonalProjection {Y : Type*} [Fintype Y]
    [DecidableEq Y] {p : Matrix Y Y ℂ} (hp : IsOrthogonalProjectionMatrix p) :
    (p.trace).re = (p.rank : ℝ) := by
  have hidem : IsIdempotentElem p.mulVecLin := by
    show p.mulVecLin * p.mulVecLin = p.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hp.2]
  have hproj : LinearMap.IsProj (LinearMap.range p.mulVecLin) p.mulVecLin :=
    LinearMap.IsIdempotentElem.isProj_range _ hidem
  have htr : LinearMap.trace ℂ (Y → ℂ) p.mulVecLin = ((p.rank : ℕ) : ℂ) :=
    hproj.trace
  have hmat : LinearMap.trace ℂ (Y → ℂ) p.mulVecLin = p.trace := by
    rw [← Matrix.toLin'_apply']
    exact Matrix.trace_toLin'_eq p
  rw [← hmat, htr]
  simp

/-! ## Exact involutions -/

/-- An *exact involution* is a self-adjoint matrix squaring to the identity. -/
def IsExactInvolution {Y : Type*} [Fintype Y] [DecidableEq Y]
    (R : Matrix Y Y ℂ) : Prop := Rᴴ = R ∧ R * R = 1

/-- The displacement of two exact involutions is self-adjoint. -/
theorem conjTranspose_sub_eq {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w) :
    (u - w)ᴴ = u - w := by
  rw [Matrix.conjTranspose_sub, hu.1, hw.1]

/-- The square of the displacement of two *commuting* exact involutions. -/
theorem sub_mul_sub_of_commute {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w)
    (hcomm : u * w = w * u) :
    (u - w) * (u - w) = (2 : ℂ) • ((1 : Matrix Y Y ℂ) - u * w) := by
  have hexp : (u - w) * (u - w) = u * u + w * w - (u * w + w * u) := by
    noncomm_ring
  rw [hexp, hu.2, hw.2, ← hcomm, two_smul]
  abel

/-- The displacement of two commuting exact involutions is reversed by the
product of the pair. -/
theorem sub_mul_mul_eq_neg_sub {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w)
    (hcomm : u * w = w * u) : (u - w) * (u * w) = -(u - w) := by
  have hexp : (u - w) * (u * w) = u * u * w - w * u * w := by noncomm_ring
  rw [hexp, hu.2, one_mul, ← hcomm, Matrix.mul_assoc, hw.2, mul_one]
  abel

/-- **The cubic relation.**  The displacement `T` of two commuting exact
involutions satisfies `T³ = 4 T`; this is what makes `T² / 4` idempotent. -/
theorem sub_mul_sub_mul_sub {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w)
    (hcomm : u * w = w * u) :
    (u - w) * ((u - w) * (u - w)) = (4 : ℂ) • (u - w) := by
  calc
    (u - w) * ((u - w) * (u - w))
        = (u - w) * ((2 : ℂ) • ((1 : Matrix Y Y ℂ) - u * w)) := by
      rw [sub_mul_sub_of_commute hu hw hcomm]
    _ = (2 : ℂ) • ((u - w) * ((1 : Matrix Y Y ℂ) - u * w)) :=
      Matrix.mul_smul _ _ _
    _ = (2 : ℂ) • ((u - w) - (u - w) * (u * w)) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    _ = (2 : ℂ) • ((2 : ℂ) • (u - w)) := by
      rw [sub_mul_mul_eq_neg_sub hu hw hcomm, sub_neg_eq_add,
        ← two_smul ℂ (u - w)]
    _ = (4 : ℂ) • (u - w) := by
      rw [smul_smul]
      norm_num

/-! ## The half-square projection -/

/-- The *half-square projection* of a pair of matrices: a quarter of the square
of their displacement.  For a commuting pair of exact involutions this is an
orthogonal projection, and its rank is the rank displacement of the pair. -/
noncomputable def halfSqProjection {Y : Type*} [Fintype Y] [DecidableEq Y]
    (u w : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (4 : ℂ)⁻¹ • ((u - w) * (u - w))

/-- The half-square projection of a commuting pair of exact involutions is an
orthogonal projection matrix. -/
theorem halfSqProjection_isOrthogonalProjection {Y : Type*} [Fintype Y]
    [DecidableEq Y] {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u)
    (hw : IsExactInvolution w) (hcomm : u * w = w * u) :
    IsOrthogonalProjectionMatrix (halfSqProjection u w) := by
  constructor
  · show ((4 : ℂ)⁻¹ • ((u - w) * (u - w)))ᴴ = (4 : ℂ)⁻¹ • ((u - w) * (u - w))
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      conjTranspose_sub_eq hu hw]
    simp
  · show ((4 : ℂ)⁻¹ • ((u - w) * (u - w))) * ((4 : ℂ)⁻¹ • ((u - w) * (u - w))) =
      (4 : ℂ)⁻¹ • ((u - w) * (u - w))
    have hquad : ((u - w) * (u - w)) * ((u - w) * (u - w)) =
        (4 : ℂ) • ((u - w) * (u - w)) := by
      calc
        ((u - w) * (u - w)) * ((u - w) * (u - w))
            = (u - w) * ((u - w) * ((u - w) * (u - w))) := by
          rw [Matrix.mul_assoc]
        _ = (u - w) * ((4 : ℂ) • (u - w)) := by
          rw [sub_mul_sub_mul_sub hu hw hcomm]
        _ = (4 : ℂ) • ((u - w) * (u - w)) := Matrix.mul_smul _ _ _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hquad, smul_smul]
    norm_num

/-- The half-square projection fixes the displacement it is built from. -/
theorem sub_mul_halfSqProjection {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w)
    (hcomm : u * w = w * u) :
    (u - w) * halfSqProjection u w = u - w := by
  show (u - w) * ((4 : ℂ)⁻¹ • ((u - w) * (u - w))) = u - w
  rw [Matrix.mul_smul, sub_mul_sub_mul_sub hu hw hcomm, smul_smul]
  norm_num

/-- The half-square projection has exactly the rank of the displacement, so the
projection rank and the rank displacement are the same invariant. -/
theorem rank_halfSqProjection {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w)
    (hcomm : u * w = w * u) :
    (halfSqProjection u w).rank = (u - w).rank := by
  refine le_antisymm ?_ ?_
  · have hfac : halfSqProjection u w = (u - w) * ((4 : ℂ)⁻¹ • (u - w)) := by
      show (4 : ℂ)⁻¹ • ((u - w) * (u - w)) = _
      rw [Matrix.mul_smul]
    rw [hfac]
    exact Matrix.rank_mul_le_left _ _
  · calc
      (u - w).rank = ((u - w) * halfSqProjection u w).rank := by
        rw [sub_mul_halfSqProjection hu hw hcomm]
      _ ≤ (halfSqProjection u w).rank := Matrix.rank_mul_le_right _ _

/-- **Mass equals four times rank.**  For a commuting pair of exact involutions
the unnormalized Frobenius mass of the displacement is exactly four times the
rank of the half-square projection — an identity, not an estimate. -/
theorem matMass_sub_eq_four_mul_rank {Y : Type*} [Fintype Y] [DecidableEq Y]
    {u w : Matrix Y Y ℂ} (hu : IsExactInvolution u) (hw : IsExactInvolution w)
    (hcomm : u * w = w * u) :
    ScaledKazhdanTransport.matMass (u - w) =
      4 * ((halfSqProjection u w).rank : ℝ) := by
  have hP : (u - w) * (u - w) = (4 : ℂ) • halfSqProjection u w := by
    show _ = (4 : ℂ) • ((4 : ℂ)⁻¹ • ((u - w) * (u - w)))
    rw [smul_smul]
    norm_num
  calc
    ScaledKazhdanTransport.matMass (u - w) = (((u - w)ᴴ * (u - w)).trace).re :=
      matMass_eq_re_trace_conjTranspose_mul _
    _ = (((4 : ℂ) • halfSqProjection u w).trace).re := by
      rw [conjTranspose_sub_eq hu hw, hP]
    _ = ((4 : ℂ) * (halfSqProjection u w).trace).re := by
      rw [Matrix.trace_smul, smul_eq_mul]
    _ = 4 * ((halfSqProjection u w).trace).re := by
      rw [Complex.mul_re]
      norm_num
    _ = 4 * ((halfSqProjection u w).rank : ℝ) := by
      rw [re_trace_eq_rank_of_isOrthogonalProjection
        (halfSqProjection_isOrthogonalProjection hu hw hcomm)]

/-! ## Rank rigidity for nearby projections -/

/-- Compression by a matrix at operator distance less than `1` from an
orthogonal projection is injective on the range of that projection, so the
projection's rank is bounded by the rank of the nearby matrix. -/
theorem rank_le_of_norm_sub_lt_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    {p q : Matrix Y Y ℂ} (hp : IsOrthogonalProjectionMatrix p)
    (hlt : ‖p - q‖ < 1) : p.rank ≤ q.rank := by
  let f : LinearMap.range p.mulVecLin →ₗ[ℂ] LinearMap.range q.mulVecLin :=
    LinearMap.codRestrict _ (q.mulVecLin.comp (LinearMap.range p.mulVecLin).subtype)
      (fun x ↦ LinearMap.mem_range_self _ _)
  have hf_apply : ∀ x : LinearMap.range p.mulVecLin,
      (f x : Y → ℂ) = q *ᵥ (x : Y → ℂ) := fun _ ↦ rfl
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have hzero : q *ᵥ (x : Y → ℂ) = 0 := by
      have hker := congrArg (Subtype.val) (LinearMap.mem_ker.mp hx)
      simpa [hf_apply] using hker
    have hfix : p *ᵥ (x : Y → ℂ) = (x : Y → ℂ) :=
      mulVec_eq_self_of_mem_range hp x.2
    have hval : (p - q) *ᵥ (x : Y → ℂ) = (x : Y → ℂ) := by
      rw [Matrix.sub_mulVec, hfix, hzero, sub_zero]
    have hbound := sum_normSq_mulVec_le_general (p - q) (x : Y → ℂ)
    rw [hval] at hbound
    have hnn : 0 ≤ ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) :=
      Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
    have hsq : ‖p - q‖ ^ 2 < 1 := by nlinarith [norm_nonneg (p - q)]
    have hle : ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) ≤ 0 := by nlinarith
    have hzerosum : ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) = 0 :=
      le_antisymm hle hnn
    have hxz : (x : Y → ℂ) = 0 := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) ↦ Complex.normSq_nonneg
          ((x : Y → ℂ) j))).mp hzerosum i (Finset.mem_univ i)
      exact Complex.normSq_eq_zero.mp hi
    exact Subtype.ext hxz
  exact LinearMap.finrank_le_finrank_of_injective hf_inj

/-- **Rank rigidity.**  Two orthogonal projection matrices at operator distance
strictly less than `1` have equal rank. -/
theorem rank_eq_of_projections_close {Y : Type*} [Fintype Y] [DecidableEq Y]
    {p q : Matrix Y Y ℂ} (hp : IsOrthogonalProjectionMatrix p)
    (hq : IsOrthogonalProjectionMatrix q) (hlt : ‖p - q‖ < 1) :
    p.rank = q.rank := by
  have hsymm : ‖q - p‖ < 1 := by rwa [norm_sub_rev]
  exact le_antisymm (rank_le_of_norm_sub_lt_one hp hlt)
    (rank_le_of_norm_sub_lt_one hq hsymm)

/-! ## The reverse comparison -/

/-- **Mass is at most rank times the squared operator norm.**  Summing the
Frobenius mass along an eigenbasis of the Gram matrix `Tᴴ T` turns it into the
sum of the eigenvalues; each eigenvalue is at most `‖T‖²`, and the number of
nonzero ones is the rank of the Gram matrix, which is at most the rank of `T`.
-/
theorem matMass_le_rank_mul_sq_opNorm {Y : Type*} [Fintype Y] [DecidableEq Y]
    (T : Matrix Y Y ℂ) :
    ScaledKazhdanTransport.matMass T ≤ (T.rank : ℝ) * ‖T‖ ^ 2 := by
  have hA : (Tᴴ * T).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self T
  have hUmem : (hA.eigenvectorUnitary : Matrix Y Y ℂ) ∈
      Matrix.unitaryGroup Y ℂ := hA.eigenvectorUnitary.2
  have hUstar : (hA.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix Y Y ℂ) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hUmem
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUstar' : (hA.eigenvectorUnitary : Matrix Y Y ℂ) *
      (hA.eigenvectorUnitary : Matrix Y Y ℂ)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hUmem
    rwa [Matrix.star_eq_conjTranspose] at h
  -- the mass of the image of an eigenvector is the corresponding eigenvalue
  have heig : ∀ j : Y,
      ∑ i : Y, Complex.normSq ((T *ᵥ ⇑(hA.eigenvectorBasis j)) i) =
        hA.eigenvalues j := by
    intro j
    rw [sum_normSq_mulVec_eq_re_gram_general T]
    exact (hA.eigenvalues_eq j).symm
  -- the eigenvectors are the columns of the eigenvector unitary
  have hvec : ∀ j : Y, (fun k ↦ (hA.eigenvectorUnitary : Matrix Y Y ℂ) k j) =
      ⇑(hA.eigenvectorBasis j) :=
    fun j ↦ funext fun k ↦ hA.eigenvectorUnitary_apply k j
  have hcolunit : ∀ j : Y,
      ∑ i : Y, Complex.normSq ((⇑(hA.eigenvectorBasis j) : Y → ℂ) i) = 1 := by
    intro j
    have hmv := sum_normSq_mulVec_of_star_mul_self hUstar (Pi.single j (1 : ℂ))
    rw [hA.eigenvectorUnitary_mulVec j] at hmv
    refine hmv.trans ?_
    rw [Finset.sum_eq_single j (fun b _ hb ↦ by simp [hb])
      (fun hj ↦ absurd (Finset.mem_univ j) hj)]
    simp
  have hcolbound : ∀ j : Y, hA.eigenvalues j ≤ ‖T‖ ^ 2 := by
    intro j
    have h := sum_normSq_mulVec_le_general T (⇑(hA.eigenvectorBasis j) : Y → ℂ)
    rw [heig j, hcolunit j, mul_one] at h
    exact h
  -- the columns of `T * U` carry the eigenvalues as their masses
  have hcolmass : ∀ j : Y,
      ∑ i : Y, Complex.normSq
          ((T * (hA.eigenvectorUnitary : Matrix Y Y ℂ)) i j) =
        hA.eigenvalues j := by
    intro j
    have hentry : ∀ i : Y,
        (T * (hA.eigenvectorUnitary : Matrix Y Y ℂ)) i j =
          (T *ᵥ fun k ↦ (hA.eigenvectorUnitary : Matrix Y Y ℂ) k j) i := by
      intro i
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    calc
      ∑ i : Y, Complex.normSq
            ((T * (hA.eigenvectorUnitary : Matrix Y Y ℂ)) i j)
          = ∑ i : Y, Complex.normSq ((T *ᵥ ⇑(hA.eigenvectorBasis j)) i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hentry i, hvec j]
      _ = hA.eigenvalues j := heig j
  have hmass : ScaledKazhdanTransport.matMass T = ∑ j : Y, hA.eigenvalues j := by
    have hright := ScaledKazhdanTransport.matMass_mul_right_of_mul_star_self
      hUstar' T
    calc
      ScaledKazhdanTransport.matMass T
          = ScaledKazhdanTransport.matMass
              (T * (hA.eigenvectorUnitary : Matrix Y Y ℂ)) := hright.symm
      _ = ∑ i : Y, ∑ j : Y, Complex.normSq
            ((T * (hA.eigenvectorUnitary : Matrix Y Y ℂ)) i j) := rfl
      _ = ∑ j : Y, ∑ i : Y, Complex.normSq
            ((T * (hA.eigenvectorUnitary : Matrix Y Y ℂ)) i j) := Finset.sum_comm
      _ = ∑ j : Y, hA.eigenvalues j := Finset.sum_congr rfl fun j _ ↦ hcolmass j
  -- only the nonzero eigenvalues contribute, and there are `rank` many
  have hsum : ∑ j : Y, hA.eigenvalues j =
      ∑ j ∈ Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0),
        hA.eigenvalues j := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x _ hx
    by_contra hne
    exact hx (Finset.mem_filter.2 ⟨Finset.mem_univ x, hne⟩)
  have hcard :
      (Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0)).card =
        (Tᴴ * T).rank := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hbound :
      ∑ j ∈ Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0),
          hA.eigenvalues j ≤
        ((Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0)).card : ℝ) *
          ‖T‖ ^ 2 := by
    have h := Finset.sum_le_card_nsmul
      (Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0)) hA.eigenvalues
      (‖T‖ ^ 2) (fun j _ ↦ hcolbound j)
    simpa [nsmul_eq_mul] using h
  have hrankle : ((Tᴴ * T).rank : ℝ) ≤ (T.rank : ℝ) := by
    exact_mod_cast Matrix.rank_mul_le_right Tᴴ T
  calc
    ScaledKazhdanTransport.matMass T = ∑ j : Y, hA.eigenvalues j := hmass
    _ = ∑ j ∈ Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0),
          hA.eigenvalues j := hsum
    _ ≤ ((Finset.univ.filter (fun j ↦ hA.eigenvalues j ≠ 0)).card : ℝ) *
          ‖T‖ ^ 2 := hbound
    _ = ((Tᴴ * T).rank : ℝ) * ‖T‖ ^ 2 := by rw [hcard]
    _ ≤ (T.rank : ℝ) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hrankle (sq_nonneg _)

end InvolutionRankMass
end GroupApproximation
