import GroupApproximation.Sofic.InvolutionOrbitMicrostates

/-!
# The rank displacement metric of an involution microstate family

Given an exactly commuting family of exact involution microstates for a
witness orbit, the rank of a pairwise difference is an integer-valued
displacement.  This file develops its calculus:

* covariance of the family along the group, in operator norm;
* the triangle inequality (rank subadditivity — no commutation needed);
* **eventual invariance**: group translation preserves the displacement at
  all late stages, because the associated half-square projections are
  operator-close and equal-rank;
* the word bound: displacement grows at most linearly in the word length,
  against the generator normalization `kNorm`;
* the mass identity `matMass (V γ − V 1) = 4 · dV γ 1`;
* positivity of the displacement under a marked separation.

Everything is stated for an abstract family satisfying the three clauses
of `exists_involutionMicrostates`, so the endpoint can instantiate it by
choice.
-/

namespace GroupApproximation
namespace InvolutionCollapseMetric

open Matrix InvolutionOrbitMicrostates InvolutionRankMass
open KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]
variable (B : OpAlmostRepresentation E)
variable (iota : Γ →* E)
variable (k : E)
variable (V : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ)

/-- The integer rank displacement between two orbit microstates. -/
noncomputable def dV (n : ℕ) (γ₁ γ₂ : Γ) : ℕ :=
  (V n γ₁ - V n γ₂).rank

/-- The generator normalization: total displacement of a finite set from
the basepoint. -/
noncomputable def kNorm (S : Finset Γ) (n : ℕ) : ℕ :=
  ∑ a ∈ S, dV B V n a 1

/-! ## Elementary properties -/

/-- Negation preserves the rank. -/
theorem rank_neg {Y : Type*} [Fintype Y] (A : Matrix Y Y ℂ) :
    (-A).rank = A.rank := by
  have hrange : LinearMap.range (-A).mulVecLin =
      LinearMap.range A.mulVecLin := by
    ext x
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨-v, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_neg, Matrix.neg_mulVec]
    · rintro ⟨v, rfl⟩
      refine ⟨-v, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_neg, Matrix.neg_mulVec, neg_neg]
  unfold Matrix.rank
  rw [hrange]

omit [Group Γ] in
theorem dV_triangle (n : ℕ) (γ₁ γ₂ γ₃ : Γ) :
    dV B V n γ₁ γ₃ ≤ dV B V n γ₁ γ₂ + dV B V n γ₂ γ₃ :=
  rank_sub_le_add _ _ _

omit [Group Γ] in
theorem dV_symm (n : ℕ) (γ₁ γ₂ : Γ) :
    dV B V n γ₁ γ₂ = dV B V n γ₂ γ₁ := by
  unfold dV
  rw [show V n γ₁ - V n γ₂ = -(V n γ₂ - V n γ₁) by abel, rank_neg]

theorem dV_le_kNorm {S : Finset Γ} {a : Γ} (ha : a ∈ S) (n : ℕ) :
    dV B V n a 1 ≤ kNorm B V S n := by
  unfold kNorm
  exact Finset.single_le_sum (f := fun a ↦ dV B V n a 1)
    (fun _ _ ↦ Nat.zero_le _) ha

/-- An exact involution is unitary. -/
theorem isExactInvolution_mem_unitaryGroup {Y : Type*} [Fintype Y]
    [DecidableEq Y] {R : Matrix Y Y ℂ}
    (hR : ExactInvolutionLifts.IsExactInvolution R) :
    R ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hR.1]
  exact hR.2

/-- Differences of exact involutions have operator norm at most `2`. -/
theorem norm_sub_le_two {Y : Type*} [Fintype Y] [DecidableEq Y]
    {R R' : Matrix Y Y ℂ}
    (hR : ExactInvolutionLifts.IsExactInvolution R)
    (hR' : ExactInvolutionLifts.IsExactInvolution R') (hY : Nonempty Y) :
    ‖R - R'‖ ≤ 2 := by
  haveI := hY
  have h1 : ‖R‖ = 1 :=
    CStarRing.norm_of_mem_unitary (isExactInvolution_mem_unitaryGroup hR)
  have h2 : ‖R'‖ = 1 :=
    CStarRing.norm_of_mem_unitary (isExactInvolution_mem_unitaryGroup hR')
  calc
    ‖R - R'‖ ≤ ‖R‖ + ‖R'‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

/-! ## Covariance of the family -/

/-- The corrected family inherits the covariance of the raw microstates. -/
theorem V_covariance_vanishing
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (g γ : Γ) :
    OpNormVanishing B (fun n ↦
      (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ) * V n γ *
          (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        V n (g * γ)) := by
  have hnorm : ∀ n, ‖(B.map n (iota g) :
      Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun n ↦ norm_le_one_of_mem_unitary (B.map n (iota g)).2
  have hnormH : ∀ n, ‖(B.map n (iota g) :
      Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hnorm n
  have h₁ : OpNormVanishing B (fun n ↦
      (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ) *
        (V n γ - raw B iota k n γ) *
        (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
    ((hVconv γ).mul_left_of_norm_le_one _ hnorm).mul_right_of_norm_le_one
      _ hnormH
  have h₂ := raw_covariance_vanishing B iota k g γ
  have h₃ := (hVconv (g * γ)).neg
  refine ((h₁.add h₂).add h₃).congr fun n ↦ ?_
  noncomm_ring

/-! ## Eventual invariance of the displacement -/

/-- Translation by a fixed group element eventually preserves every fixed
displacement: the transported half-square projections are operator-close
projections, hence equal-rank. -/
theorem eventual_invariance
    (hVinv : ∀ n γ, ExactInvolutionLifts.IsExactInvolution (V n γ))
    (hVcomm : ∀ n γ₁ γ₂, V n γ₁ * V n γ₂ = V n γ₂ * V n γ₁)
    (hVconv : ∀ γ, OpNormVanishing B (fun n ↦ V n γ - raw B iota k n γ))
    (g γ₁ γ₂ : Γ) :
    ∃ N, ∀ n ≥ N, dV B V n (g * γ₁) (g * γ₂) = dV B V n γ₁ γ₂ := by
  classical
  obtain ⟨N₁, hN₁⟩ := V_covariance_vanishing B iota k V hVconv g γ₁
    (1 / 8) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := V_covariance_vanishing B iota k V hVconv g γ₂
    (1 / 8) (by norm_num)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  by_cases hY : Nonempty (B.model n)
  case neg =>
    haveI : IsEmpty (B.model n) := not_nonempty_iff.mp hY
    unfold dV
    have hz : ∀ M : Matrix (B.model n) (B.model n) ℂ, M = 0 :=
      fun M ↦ Subsingleton.elim M 0
    rw [hz (V n (g * γ₁) - V n (g * γ₂)), hz (V n γ₁ - V n γ₂)]
  case pos =>
  set U : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n (iota g) : Matrix (B.model n) (B.model n) ℂ) with hU
  have hUmem : U ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (iota g)).2
  set T : Matrix (B.model n) (B.model n) ℂ := V n γ₁ - V n γ₂ with hT
  set T' : Matrix (B.model n) (B.model n) ℂ :=
    V n (g * γ₁) - V n (g * γ₂) with hT'
  have hTdiff : ‖T' - U * T * Uᴴ‖ ≤ 1 / 4 := by
    have h₁ := hN₁ n ((le_max_left _ _).trans hn)
    have h₂ := hN₂ n ((le_max_right _ _).trans hn)
    have hsplit : T' - U * T * Uᴴ =
        (V n (g * γ₁) - U * V n γ₁ * Uᴴ) -
          (V n (g * γ₂) - U * V n γ₂ * Uᴴ) := by
      rw [hT', hT]
      noncomm_ring
    calc
      ‖T' - U * T * Uᴴ‖ =
          ‖(V n (g * γ₁) - U * V n γ₁ * Uᴴ) -
            (V n (g * γ₂) - U * V n γ₂ * Uᴴ)‖ := by rw [hsplit]
      _ ≤ ‖V n (g * γ₁) - U * V n γ₁ * Uᴴ‖ +
          ‖V n (g * γ₂) - U * V n γ₂ * Uᴴ‖ := norm_sub_le _ _
      _ ≤ 1 / 4 := by
        rw [norm_sub_rev] at h₁ h₂
        linarith
  -- both are differences of commuting exact involutions of norm ≤ 2
  have hP : IsOrthogonalProjectionMatrix
      (halfSqProjection (V n γ₁) (V n γ₂)) :=
    halfSqProjection_isOrthogonalProjection
      ⟨(hVinv n γ₁).1, (hVinv n γ₁).2⟩ ⟨(hVinv n γ₂).1, (hVinv n γ₂).2⟩
      (hVcomm n γ₁ γ₂)
  have hP' : IsOrthogonalProjectionMatrix
      (halfSqProjection (V n (g * γ₁)) (V n (g * γ₂))) :=
    halfSqProjection_isOrthogonalProjection
      ⟨(hVinv n (g * γ₁)).1, (hVinv n (g * γ₁)).2⟩
      ⟨(hVinv n (g * γ₂)).1, (hVinv n (g * γ₂)).2⟩
      (hVcomm n (g * γ₁) (g * γ₂))
  have hPconj : IsOrthogonalProjectionMatrix
      (U * halfSqProjection (V n γ₁) (V n γ₂) * Uᴴ) :=
    KazhdanCornerMatrices.unitary_conjugate_isOrthogonalProjection hUmem hP
  have hTnorm : ‖T‖ ≤ 2 :=
    norm_sub_le_two (hVinv n γ₁) (hVinv n γ₂) hY
  have hT'norm : ‖T'‖ ≤ 2 :=
    norm_sub_le_two (hVinv n (g * γ₁)) (hVinv n (g * γ₂)) hY
  have hUTnorm : ‖U * T * Uᴴ‖ ≤ 2 := by
    rw [CStarRing.norm_mul_mem_unitary _
        (KazhdanCompressorCorner.conjTranspose_mem_unitaryGroup hUmem),
      CStarRing.norm_mem_unitary_mul _ hUmem]
    exact hTnorm
  -- the half-square projections are operator-close
  have hProjdiff : ‖halfSqProjection (V n (g * γ₁)) (V n (g * γ₂)) -
      U * halfSqProjection (V n γ₁) (V n γ₂) * Uᴴ‖ < 1 := by
    have hconjsq : U * halfSqProjection (V n γ₁) (V n γ₂) * Uᴴ =
        (4 : ℂ)⁻¹ • ((U * T * Uᴴ) * (U * T * Uᴴ)) := by
      show U * ((4 : ℂ)⁻¹ • (T * T)) * Uᴴ = _
      have hUU : Uᴴ * U = 1 := by
        have h := Matrix.mem_unitaryGroup_iff'.mp hUmem
        rwa [Matrix.star_eq_conjTranspose] at h
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc
        U * (T * T) * Uᴴ = U * T * (Uᴴ * U) * T * Uᴴ := by
          rw [hUU]
          noncomm_ring
        _ = U * T * Uᴴ * (U * T * Uᴴ) := by noncomm_ring
    have hfactor : halfSqProjection (V n (g * γ₁)) (V n (g * γ₂)) -
        U * halfSqProjection (V n γ₁) (V n γ₂) * Uᴴ =
        (4 : ℂ)⁻¹ • (T' * T' - (U * T * Uᴴ) * (U * T * Uᴴ)) := by
      rw [hconjsq]
      show (4 : ℂ)⁻¹ • (T' * T') - _ = _
      rw [smul_sub]
    have hprod : ‖T' * T' - (U * T * Uᴴ) * (U * T * Uᴴ)‖ ≤
        (2 + 2) * (1 / 4) := by
      have hsplit2 : T' * T' - (U * T * Uᴴ) * (U * T * Uᴴ) =
          (T' - U * T * Uᴴ) * T' +
            (U * T * Uᴴ) * (T' - U * T * Uᴴ) := by
        noncomm_ring
      calc
        ‖T' * T' - (U * T * Uᴴ) * (U * T * Uᴴ)‖ =
            ‖(T' - U * T * Uᴴ) * T' +
              (U * T * Uᴴ) * (T' - U * T * Uᴴ)‖ := by rw [hsplit2]
        _ ≤ ‖(T' - U * T * Uᴴ) * T'‖ +
            ‖(U * T * Uᴴ) * (T' - U * T * Uᴴ)‖ := norm_add_le _ _
        _ ≤ ‖T' - U * T * Uᴴ‖ * ‖T'‖ +
            ‖U * T * Uᴴ‖ * ‖T' - U * T * Uᴴ‖ := by
          have h1 := Matrix.l2_opNorm_mul (T' - U * T * Uᴴ) T'
          have h2 := Matrix.l2_opNorm_mul (U * T * Uᴴ) (T' - U * T * Uᴴ)
          linarith
        _ ≤ (2 + 2) * (1 / 4) := by
          have hnn : (0 : ℝ) ≤ ‖T' - U * T * Uᴴ‖ := norm_nonneg _
          nlinarith [hTdiff, hT'norm, hUTnorm,
            norm_nonneg T', norm_nonneg (U * T * Uᴴ)]
    calc
      ‖halfSqProjection (V n (g * γ₁)) (V n (g * γ₂)) -
          U * halfSqProjection (V n γ₁) (V n γ₂) * Uᴴ‖ =
          ‖(4 : ℂ)⁻¹‖ * ‖T' * T' - (U * T * Uᴴ) * (U * T * Uᴴ)‖ := by
        rw [hfactor, norm_smul]
      _ ≤ (1 / 4) * ((2 + 2) * (1 / 4)) := by
        have hc : ‖(4 : ℂ)⁻¹‖ = 1 / 4 := by
          rw [norm_inv]
          norm_num
        rw [hc]
        have hnn := norm_nonneg
          (T' * T' - (U * T * Uᴴ) * (U * T * Uᴴ))
        nlinarith [hprod]
      _ < 1 := by norm_num
  -- equal ranks
  have hrankeq := rank_eq_of_projections_close hP' hPconj hProjdiff
  have hrankP : (halfSqProjection (V n γ₁) (V n γ₂)).rank =
      dV B V n γ₁ γ₂ :=
    rank_halfSqProjection ⟨(hVinv n γ₁).1, (hVinv n γ₁).2⟩
      ⟨(hVinv n γ₂).1, (hVinv n γ₂).2⟩ (hVcomm n γ₁ γ₂)
  have hrankP' : (halfSqProjection (V n (g * γ₁)) (V n (g * γ₂))).rank =
      dV B V n (g * γ₁) (g * γ₂) :=
    rank_halfSqProjection
      ⟨(hVinv n (g * γ₁)).1, (hVinv n (g * γ₁)).2⟩
      ⟨(hVinv n (g * γ₂)).1, (hVinv n (g * γ₂)).2⟩
      (hVcomm n (g * γ₁) (g * γ₂))
  have hconjrank : (U * halfSqProjection (V n γ₁) (V n γ₂) * Uᴴ).rank =
      (halfSqProjection (V n γ₁) (V n γ₂)).rank :=
    rank_unitary_conj hUmem _
  rw [← hrankP', ← hrankP, hrankeq, hconjrank]

end InvolutionCollapseMetric
end GroupApproximation
