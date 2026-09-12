import GroupApproximation.Sofic.MarkedCompressionSequentialKill
import GroupApproximation.Sofic.LeavittTraceFloor

/-!
# Coordinate averages for finite normal corners

`UniversalWeakMF` is deliberately only a quotient group, so the finite-normal
corner cannot be constructed by adding its elements there.  This file moves
the Reynolds average to the coordinate matrices of an
`OpAlmostRepresentation`.

For a finite subgroup `F ≤ E`, `subgroupAverage A F n` is the normalized
matrix average of the restricted microstate over `F`.  The lemmas below split
the finite-normal corner construction into reusable tasks:

* left and right absorption by the finite subgroup;
* asymptotic self-adjointness and idempotence;
* asymptotic centrality under the ambient group when `F` is normal;
* spectral rounding of this approximate projection and compression of the
  ambient almost representation.

The first three bullets use only finite sums of the existing operator-norm
multiplicative defects.  The final spectral-rounding/compression adapter is
consumed by `KazhdanCompressionCore.finiteNormal_le_normMFResidual`.

For provenance, the character-isotypic finite-normal corner appears in the
proof of Bachner--Dogon--Lubotzky, arXiv:2508.17392, Proposition 1.6; their
Propositions 1.5 and 2.4 provide the closely related central-involution and
dimension-changing operator-norm corner constructions.  This file gives a
native Lean implementation of the Reynolds-average version and copies no
external code.
-/

namespace GroupApproximation
namespace FiniteNormalAverageCorner

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner NegativeCornerModel
open scoped Matrix.Norms.L2Operator

variable {E : Type} [Group E]

/-- Operator-norm vanishing is preserved by a pointwise cofinal reindexing. -/
theorem OpNormVanishing.reindex {A : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x) (phi : ℕ → ℕ)
    (hphi : ∀ n, n ≤ phi n) :
    OpNormVanishing (A.reindex phi hphi) (fun n ↦ x (phi n)) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hx epsilon hepsilon
  exact ⟨N, fun n hn ↦ hN (phi n) (hn.trans (hphi n))⟩

section Average

variable (A : OpAlmostRepresentation E) (F : Subgroup E) [Fintype F]

/-- The restricted operator-norm almost representation of the finite
subgroup. -/
abbrev restricted : OpAlmostRepresentation F :=
  A.comap F.subtype

/-- The coordinate Reynolds average of the finite subgroup. -/
noncomputable def subgroupAverage (n : ℕ) :
    Matrix (A.model n) (A.model n) ℂ :=
  matrixAverage (restricted A F) Finset.univ n

/-- Left multiplication permutes the finite subgroup sum. -/
theorem sum_map_mul_left (f : F) (n : ℕ) :
    (∑ x : F, ((restricted A F).map n (f * x) :
      Matrix (A.model n) (A.model n) ℂ)) =
      ∑ x : F, ((restricted A F).map n x :
        Matrix (A.model n) (A.model n) ℂ) :=
  Fintype.sum_equiv (Equiv.mulLeft f) _ _ fun _ ↦ rfl

/-- Right multiplication permutes the finite subgroup sum. -/
theorem sum_map_mul_right (f : F) (n : ℕ) :
    (∑ x : F, ((restricted A F).map n (x * f) :
      Matrix (A.model n) (A.model n) ℂ)) =
      ∑ x : F, ((restricted A F).map n x :
        Matrix (A.model n) (A.model n) ℂ) :=
  Fintype.sum_equiv (Equiv.mulRight f) _ _ fun _ ↦ rfl

/-- The finite subgroup average has operator norm at most one. -/
theorem norm_subgroupAverage_le_one (n : ℕ) :
    ‖subgroupAverage A F n‖ ≤ 1 :=
  norm_matrixAverage_le_one (restricted A F) Finset.univ n

/-- Every finite-subgroup microstate asymptotically absorbs the Reynolds
average on the left. -/
theorem map_mul_subgroupAverage_sub_vanishing (f : F) :
    OpNormVanishing A (fun n ↦
      (A.map n f : Matrix (A.model n) (A.model n) ℂ) *
        subgroupAverage A F n - subgroupAverage A F n) := by
  let R := restricted A F
  have hsum : OpNormVanishing R (fun n ↦
      ∑ x : F, ((R.map n f : Matrix (R.model n) (R.model n) ℂ) *
        R.map n x - R.map n (f * x))) := by
    simpa only [Finset.sum_sub_distrib] using
      OpNormVanishing.finset_sum (A := R) Finset.univ
        (fun x n ↦ (R.map n f : Matrix (R.model n) (R.model n) ℂ) *
          R.map n x - R.map n (f * x))
        (fun x _ ↦ (multiplicativeDefect_vanishing R f x).neg.congr
          (fun _ ↦ by abel))
  have hscaled := hsum.smul ((Fintype.card F : ℂ)⁻¹)
  change OpNormVanishing A _ at hscaled
  refine hscaled.congr fun n ↦ ?_
  simp only [R, restricted, subgroupAverage, matrixAverage, Finset.card_univ]
  rw [Finset.sum_sub_distrib, sum_map_mul_left A F f n, smul_sub,
    ← Finset.mul_sum, ← Matrix.mul_smul]
  rfl

/-- The finite subgroup average is asymptotically idempotent. -/
theorem subgroupAverage_idempotent_vanishing :
    OpNormVanishing A (fun n ↦
      subgroupAverage A F n * subgroupAverage A F n -
        subgroupAverage A F n) := by
  have hsum : OpNormVanishing A (fun n ↦
      ∑ f : F, ((A.map n f : Matrix (A.model n) (A.model n) ℂ) *
        subgroupAverage A F n - subgroupAverage A F n)) :=
    OpNormVanishing.finset_sum (A := A) (Finset.univ : Finset F)
      (fun f n ↦ (A.map n f : Matrix (A.model n) (A.model n) ℂ) *
        subgroupAverage A F n - subgroupAverage A F n)
      (fun f _ ↦ map_mul_subgroupAverage_sub_vanishing A F f)
  have hscaled := hsum.smul ((Fintype.card F : ℂ)⁻¹)
  refine hscaled.congr fun n ↦ ?_
  have hcard : ((Fintype.card F : ℂ)) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  simp only [subgroupAverage, matrixAverage, Finset.card_univ]
  rw [Finset.sum_sub_distrib, smul_sub, ← Finset.sum_mul,
    ← Matrix.smul_mul, Finset.sum_const]
  simp only [Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcoef : (Fintype.card F : ℂ)⁻¹ *
      ((Fintype.card F : ℂ) * (Fintype.card F : ℂ)⁻¹) =
        (Fintype.card F : ℂ)⁻¹ := by
    field_simp
  rw [hcoef]
  rfl

/-- Exact Hermitian symmetrization of the finite subgroup average. -/
noncomputable def hermitianSubgroupAverage (n : ℕ) :
    Matrix (A.model n) (A.model n) ℂ :=
  hermitianAverage (restricted A F) Finset.univ n

theorem hermitianSubgroupAverage_isHermitian (n : ℕ) :
    (hermitianSubgroupAverage A F n).IsHermitian :=
  hermitianAverage_conjTranspose (restricted A F) Finset.univ n

theorem norm_hermitianSubgroupAverage_le_one (n : ℕ) :
    ‖hermitianSubgroupAverage A F n‖ ≤ 1 :=
  norm_hermitianAverage_le_one (restricted A F) Finset.univ n

/-- Hermitianization changes the finite subgroup average by operator-norm
vanishing error. -/
theorem subgroupAverage_sub_hermitian_vanishing :
    OpNormVanishing A (fun n ↦ subgroupAverage A F n -
      hermitianSubgroupAverage A F n) := by
  change OpNormVanishing (restricted A F) (fun n ↦ subgroupAverage A F n -
    hermitianSubgroupAverage A F n)
  simpa [subgroupAverage, hermitianSubgroupAverage, restricted] using
    matrixAverage_sub_hermitian_vanishing (restricted A F) Finset.univ
      (fun _ _ ↦ Finset.mem_univ _)

/-- The Hermitianized finite subgroup average remains asymptotically
idempotent. -/
theorem hermitianSubgroupAverage_idempotent_vanishing :
    OpNormVanishing A (fun n ↦
      hermitianSubgroupAverage A F n * hermitianSubgroupAverage A F n -
        hermitianSubgroupAverage A F n) := by
  let P := fun n ↦ subgroupAverage A F n
  let H := fun n ↦ hermitianSubgroupAverage A F n
  have hPH : OpNormVanishing A (fun n ↦ P n - H n) :=
    subgroupAverage_sub_hermitian_vanishing A F
  have hHP : OpNormVanishing A (fun n ↦ H n - P n) :=
    hPH.neg.congr fun _ ↦ by abel
  have hright : OpNormVanishing A (fun n ↦ (H n - P n) * H n) :=
    hHP.mul_right_of_norm_le_one H
      (norm_hermitianSubgroupAverage_le_one A F)
  have hleft : OpNormVanishing A (fun n ↦ P n * (H n - P n)) :=
    hHP.mul_left_of_norm_le_one P (norm_subgroupAverage_le_one A F)
  have hidem : OpNormVanishing A (fun n ↦ P n * P n - P n) :=
    subgroupAverage_idempotent_vanishing A F
  refine (((hright.add hleft).add hidem).add hPH).congr fun n ↦ ?_
  dsimp only [P, H]
  noncomm_ring

/-- Scalar rounding at `1/2` is controlled by twice the idempotence defect
on the closed unit interval. -/
theorem abs_indicator_sub_le_two_abs_sq_sub_self {lambda : ℝ}
    (hlambda : |lambda| ≤ 1) :
    |(if (1 / 2 : ℝ) < lambda then 1 else 0) - lambda| ≤
      2 * |lambda ^ 2 - lambda| := by
  have hlower : -1 ≤ lambda := (abs_le.mp hlambda).1
  have hupper : lambda ≤ 1 := (abs_le.mp hlambda).2
  by_cases hhalf : (1 / 2 : ℝ) < lambda
  · rw [if_pos hhalf, abs_of_nonneg (sub_nonneg.mpr hupper),
      abs_of_nonpos]
    · nlinarith [mul_nonneg (show 0 ≤ 1 - lambda by linarith)
        (show 0 ≤ 2 * lambda - 1 by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ lambda by linarith)
        (show 0 ≤ 1 - lambda by linarith)]
  · rw [if_neg hhalf]
    have hle : lambda ≤ 1 / 2 := le_of_not_gt hhalf
    by_cases hnonneg : 0 ≤ lambda
    · rw [zero_sub, abs_neg, abs_of_nonneg hnonneg, abs_of_nonpos]
      · nlinarith [mul_nonneg hnonneg (show 0 ≤ 1 - lambda by linarith)]
      · nlinarith [mul_nonneg hnonneg (show 0 ≤ 1 - lambda by linarith)]
    · have hneg : lambda < 0 := lt_of_not_ge hnonneg
      rw [zero_sub, abs_neg, abs_of_nonpos hneg.le, abs_of_nonneg]
      · nlinarith [sq_nonneg lambda]
      · nlinarith [sq_nonneg lambda]

/-- A Hermitian eigenvalue's idempotence defect is bounded by the operator
norm of the matrix idempotence defect. -/
theorem abs_hermitianEigenvalue_sq_sub_self_le
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (i : Y) :
    |(hH.eigenvalues i) ^ 2 - hH.eigenvalues i| ≤ ‖H * H - H‖ := by
  let x : EuclideanSpace ℂ Y := hH.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have hi : H *ᵥ (x : Y → ℂ) =
      ((hH.eigenvalues i : ℝ) : ℂ) • (x : Y → ℂ) :=
    hH.mulVec_eigenvectorBasis i
  have heigen :
      (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (H * H - H) x =
        ((((hH.eigenvalues i) ^ 2 - hH.eigenvalues i : ℝ) : ℂ)) • x := by
    apply PiLp.ext
    intro j
    change ((H * H - H) *ᵥ (x : Y → ℂ)) j =
      ((((((hH.eigenvalues i) ^ 2 - hH.eigenvalues i : ℝ) : ℂ)) •
        (x : Y → ℂ)) j)
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hi, mulVec_smul, hi]
    simp
    ring
  have happly := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (H * H - H)) x
  rw [heigen, norm_smul, hx, mul_one,
    Matrix.l2_opNorm_toEuclideanCLM] at happly
  calc
    |(hH.eigenvalues i) ^ 2 - hH.eigenvalues i| =
        ‖((((hH.eigenvalues i) ^ 2 - hH.eigenvalues i : ℝ) : ℂ))‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖H * H - H‖ := by simpa only [mul_one] using happly

/-- Spectral rounding of the Hermitian finite-subgroup average at threshold
`1/2`. -/
noncomputable def subgroupProjection (n : ℕ) :
    Matrix (A.model n) (A.model n) ℂ :=
  spectralAbove (hermitianSubgroupAverage A F n)
    (hermitianSubgroupAverage_isHermitian A F n) (1 / 2)

theorem subgroupProjection_isOrthogonalProjection (n : ℕ) :
    IsOrthogonalProjectionMatrix (subgroupProjection A F n) :=
  spectralAbove_isOrthogonalProjection
    (hermitianSubgroupAverage A F n)
    (hermitianSubgroupAverage_isHermitian A F n) (1 / 2)

/-- Dimension-free spectral rounding estimate for the finite subgroup
average. -/
theorem norm_subgroupProjection_sub_hermitian_le (n : ℕ) :
    ‖subgroupProjection A F n - hermitianSubgroupAverage A F n‖ ≤
      2 * ‖hermitianSubgroupAverage A F n *
        hermitianSubgroupAverage A F n - hermitianSubgroupAverage A F n‖ := by
  let H : Matrix (A.model n) (A.model n) ℂ :=
    hermitianSubgroupAverage A F n
  let hH : H.IsHermitian := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  let P : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦ if (1 / 2 : ℝ) < hH.eigenvalues i then 1 else 0)
  let L : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let R : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦
      (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) -
        (hH.eigenvalues i : ℂ))
  have hHdiag : H = V * L * Vᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = V * L * Vᴴ := by rfl
  have hPdef : subgroupProjection A F n = V * P * Vᴴ := by
    rfl
  have hcore : P - L = R := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [P, L, R]
    · simp [P, L, R, hij]
  have hrewrite : subgroupProjection A F n -
      hermitianSubgroupAverage A F n = V * R * Vᴴ := by
    change subgroupProjection A F n - H = V * R * Vᴴ
    rw [hPdef, hHdiag]
    calc
      V * P * Vᴴ - V * L * Vᴴ = V * (P - L) * Vᴴ := by
        noncomm_ring
      _ = V * R * Vᴴ := by rw [hcore]
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  rw [hrewrite, CStarRing.norm_mul_mem_unitary _ hVstar,
    CStarRing.norm_mem_unitary_mul _ hH.eigenvectorUnitary.2]
  change ‖R‖ ≤ 2 * ‖H * H - H‖
  change ‖Matrix.diagonal (fun i ↦
    (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) -
      (hH.eigenvalues i : ℂ))‖ ≤ 2 * ‖H * H - H‖
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num)
    (norm_nonneg _))).2 fun i ↦ ?_
  have hcast :
      (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) -
          (hH.eigenvalues i : ℂ) =
        (((if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℝ) else 0) -
          hH.eigenvalues i : ℝ) : ℂ) := by
    split <;> norm_num
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_indicator_sub_le_two_abs_sq_sub_self
      ((abs_hermitianEigenvalue_le_norm H hH i).trans
        (norm_hermitianSubgroupAverage_le_one A F n))).trans
    (mul_le_mul_of_nonneg_left
      (abs_hermitianEigenvalue_sq_sub_self_le H hH i) (by norm_num))

/-- The rounded projection converges to the Hermitian finite-group average. -/
theorem subgroupProjection_sub_hermitian_vanishing :
    OpNormVanishing A (fun n ↦ subgroupProjection A F n -
      hermitianSubgroupAverage A F n) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hermitianSubgroupAverage_idempotent_vanishing A F
    (epsilon / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  exact (norm_subgroupProjection_sub_hermitian_le A F n).trans
    (by nlinarith [hN n hn])

/-- The rounded projection converges to the original finite-group average. -/
theorem subgroupProjection_sub_average_vanishing :
    OpNormVanishing A (fun n ↦ subgroupProjection A F n -
      subgroupAverage A F n) := by
  have hPH := subgroupProjection_sub_hermitian_vanishing A F
  have hHA : OpNormVanishing A (fun n ↦
      hermitianSubgroupAverage A F n - subgroupAverage A F n) :=
    (subgroupAverage_sub_hermitian_vanishing A F).neg.congr
      (fun n ↦ by rw [neg_sub])
  exact (hPH.add hHA).congr fun _ ↦ by abel

/-- Complementary finite-normal spectral corner. -/
noncomputable def subgroupComplementProjection (n : ℕ) :
    Matrix (A.model n) (A.model n) ℂ :=
  1 - subgroupProjection A F n

end Average

section SurvivingCorner

variable (F : Subgroup E) [Fintype F] (f : F)
  (A : MarkedOpAlmostRepresentation E (f : E))

/-- A uniformly surviving element of the finite subgroup forces the
complementary averaging corner to be nonzero at all sufficiently late
coordinates. -/
theorem subgroupComplementProjection_eventually_ne_zero :
    ∃ N, ∀ n ≥ N,
      subgroupComplementProjection A.toOpAlmostRepresentation F n ≠ 0 := by
  let B := A.toOpAlmostRepresentation
  let delta := A.separation
  have hdelta : 0 < delta := A.separation_pos
  obtain ⟨N₁, hN₁⟩ :=
    map_mul_subgroupAverage_sub_vanishing B F f
      (delta / 8) (by positivity)
  obtain ⟨N₂, hN₂⟩ :=
    subgroupProjection_sub_average_vanishing B F
      (delta / 8) (by positivity)
  obtain ⟨N₃, hN₃⟩ :=
    map_one_vanishing B (delta / 8) (by positivity)
  refine ⟨max N₁ (max N₂ N₃), fun n hn hzero ↦ ?_⟩
  have hn₁ : n ≥ N₁ := (le_max_left _ _).trans hn
  have hn₂ : n ≥ N₂ :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hn₃ : n ≥ N₃ :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  let U : Matrix (B.model n) (B.model n) ℂ := B.map n (f : E)
  let Uone : Matrix (B.model n) (B.model n) ℂ := B.map n 1
  let P : Matrix (B.model n) (B.model n) ℂ := subgroupProjection B F n
  let M : Matrix (B.model n) (B.model n) ℂ := subgroupAverage B F n
  have hPone : P = 1 := by
    have : (1 : Matrix (B.model n) (B.model n) ℂ) - P = 0 := by
      simpa [subgroupComplementProjection, P] using hzero
    exact (sub_eq_zero.mp this).symm
  have hUM : ‖U * M - M‖ ≤ delta / 8 := by
    simpa [U, M] using hN₁ n hn₁
  have hPM : ‖P - M‖ ≤ delta / 8 := by
    simpa [P, M] using hN₂ n hn₂
  have hOne : ‖Uone - 1‖ ≤ delta / 8 := by
    simpa [Uone] using hN₃ n hn₃
  have hUunitary : U ∈ Matrix.unitaryGroup (B.model n) ℂ :=
    (B.map n (f : E)).2
  have hUsub : ‖U - 1‖ ≤ 3 * (delta / 8) := by
    have hdecomp : U - 1 =
        U * (P - M) + (U * M - M) + (M - P) := by
      rw [hPone]
      noncomm_ring
    rw [hdecomp]
    calc
      ‖U * (P - M) + (U * M - M) + (M - P)‖ ≤
          ‖U * (P - M)‖ + ‖U * M - M‖ + ‖M - P‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖P - M‖ + ‖U * M - M‖ + ‖M - P‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ hUunitary]
      _ ≤ delta / 8 + delta / 8 + delta / 8 := by
        exact add_le_add (add_le_add hPM hUM)
          (by simpa [norm_sub_rev] using hPM)
      _ = 3 * (delta / 8) := by ring
  have hsepUpper : ‖U - Uone‖ ≤ delta / 2 := by
    have hdecomp : U - Uone = (U - 1) + (1 - Uone) := by abel
    rw [hdecomp]
    calc
      ‖(U - 1) + (1 - Uone)‖ ≤ ‖U - 1‖ + ‖1 - Uone‖ :=
        norm_add_le _ _
      _ ≤ 3 * (delta / 8) + delta / 8 := by
        exact add_le_add hUsub (by simpa [norm_sub_rev] using hOne)
      _ = delta / 2 := by ring
  have hsepLower : delta ≤ ‖U - Uone‖ := by
    simpa [B, delta, U, Uone] using A.marked_separated n
  linarith

end SurvivingCorner

section Normal

variable (A : OpAlmostRepresentation E) (F : Subgroup E)
  [Fintype F] [F.Normal]

/-- Conjugation by an ambient group element permutes the finite normal
subgroup sum. -/
theorem sum_map_conjNormal (g : E) (n : ℕ) :
    (∑ f : F, (A.map n ((MulAut.conjNormal (H := F) g f : F) : E) :
      Matrix (A.model n) (A.model n) ℂ)) =
      ∑ f : F, (A.map n (f : E) : Matrix (A.model n) (A.model n) ℂ) :=
  Fintype.sum_equiv (MulAut.conjNormal (H := F) g).toEquiv _ _ fun _ ↦ rfl

/-- Normality makes the finite subgroup average asymptotically central under
the ambient almost representation. -/
theorem subgroupAverage_conjugation_vanishing (g : E) :
    OpNormVanishing A (fun n ↦
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
        subgroupAverage A F n *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
          subgroupAverage A F n) := by
  have hsum : OpNormVanishing A (fun n ↦
      ∑ f : F,
        ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            A.map n (f : E) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
          A.map n ((MulAut.conjNormal (H := F) g f : F) : E))) := by
    apply OpNormVanishing.finset_sum (A := A) Finset.univ
    intro f _
    simpa only [MulAut.conjNormal_apply] using
      KazhdanCompressorCorner.conj_matrix_defect_vanishing A g (f : E)
  have hscaled := hsum.smul ((Fintype.card F : ℂ)⁻¹)
  refine hscaled.congr fun n ↦ ?_
  simp only [subgroupAverage, matrixAverage, Finset.card_univ]
  rw [Finset.sum_sub_distrib, sum_map_conjNormal A F g n, smul_sub]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  rfl

/-- The rounded finite-normal projection asymptotically commutes with every
ambient microstate. -/
theorem subgroupProjection_conjugation_vanishing (g : E) :
    OpNormVanishing A (fun n ↦
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
        subgroupProjection A F n *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
          subgroupProjection A F n) := by
  have hround := subgroupProjection_sub_average_vanishing A F
  have hunitary (n : ℕ) :
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ ≤ 1 :=
    norm_le_one_of_mem_unitary (A.map n g).2
  have hunitaryStar (n : ℕ) :
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hunitary n
  have hconjRound : OpNormVanishing A (fun n ↦
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
        (subgroupProjection A F n - subgroupAverage A F n) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) :=
    (hround.mul_left_of_norm_le_one _ hunitary).mul_right_of_norm_le_one _
      hunitaryStar
  have hmiddle := subgroupAverage_conjugation_vanishing A F g
  have hback : OpNormVanishing A (fun n ↦
      subgroupAverage A F n - subgroupProjection A F n) :=
    hround.neg.congr fun n ↦ by rw [neg_sub]
  refine ((hconjRound.add hmiddle).add hback).congr fun n ↦ ?_
  noncomm_ring

end Normal

/-! ## Ambient compression to the complementary eigenspace -/

section CornerMatrices

variable (A : OpAlmostRepresentation E) (F : Subgroup E)
  [Fintype F] [F.Normal]

/-- The low-eigenvalue predicate for the complementary finite-subgroup
corner.  This is exactly the complement of the rounded projection cut. -/
abbrev subgroupCornerPredicate (n : ℕ) : A.model n → Prop :=
  movingPredicate (restricted A F) Finset.univ (1 / 2) n

noncomputable instance subgroupCornerPredicate_decidable (n : ℕ) :
    DecidablePred (subgroupCornerPredicate A F n) := Classical.decPred _

/-- The honest finite coordinate type of the complementary averaging
corner. -/
noncomputable abbrev subgroupCornerModel (n : ℕ) : FiniteModel :=
  ⟨{i : A.model n // subgroupCornerPredicate A F n i}, inferInstance,
    inferInstance⟩

/-- Conjugate an ambient microstate into the eigenbasis of the Hermitian
finite-subgroup average. -/
noncomputable def subgroupEigenbasisMicrostate (n : ℕ) (g : E) :
    Matrix (A.model n) (A.model n) ℂ :=
  let V : Matrix (A.model n) (A.model n) ℂ :=
    (hermitianSubgroupAverage_isHermitian A F n).eigenvectorUnitary
  Vᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * V

omit [F.Normal] in
theorem subgroupEigenbasisMicrostate_mem_unitaryGroup (n : ℕ) (g : E) :
    subgroupEigenbasisMicrostate A F n g ∈
      Matrix.unitaryGroup (A.model n) ℂ := by
  let hH := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  change Vᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * V ∈
    Matrix.unitaryGroup (A.model n) ℂ
  exact mul_mem (mul_mem hVstar (A.map n g).2) hH.eigenvectorUnitary.2

omit [F.Normal] in
theorem norm_subgroupEigenbasisMicrostate_eq_one (n : ℕ) (g : E) :
    ‖subgroupEigenbasisMicrostate A F n g‖ = 1 := by
  letI : Nonempty (A.model n) :=
    Fintype.card_pos_iff.mp (A.modelNonempty n)
  exact CStarRing.norm_of_mem_unitary
    (subgroupEigenbasisMicrostate_mem_unitaryGroup A F n g)

/- Ambient multiplication defects are unchanged by conjugation into the
finite-subgroup-average eigenbasis. -/
omit [F.Normal] in
theorem norm_subgroupEigenbasisMicrostate_mul_defect_eq
    (n : ℕ) (g h : E) :
    ‖subgroupEigenbasisMicrostate A F n (g * h) -
        subgroupEigenbasisMicrostate A F n g *
          subgroupEigenbasisMicrostate A F n h‖ =
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ := by
  let hH := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hVV : V * Vᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have heq : subgroupEigenbasisMicrostate A F n (g * h) -
        subgroupEigenbasisMicrostate A F n g *
          subgroupEigenbasisMicrostate A F n h =
      Vᴴ * ((A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n h : Matrix (A.model n) (A.model n) ℂ)) * V := by
    simp only [subgroupEigenbasisMicrostate]
    rw [show
      (Vᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * V) *
          (Vᴴ * (A.map n h : Matrix (A.model n) (A.model n) ℂ) * V) =
        Vᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (V * Vᴴ) * (A.map n h : Matrix (A.model n) (A.model n) ℂ) * V by
            noncomm_ring, hVV]
    noncomm_ring
  rw [heq]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    norm_unitary_conjugate hVstar
      (D := (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n h : Matrix (A.model n) (A.model n) ℂ))

/-- The uncorrected ambient corner microstate. -/
noncomputable def subgroupCornerMicrostate (n : ℕ) (g : E) :
    Matrix (subgroupCornerModel A F n) (subgroupCornerModel A F n) ℂ :=
  principalBlock (subgroupCornerPredicate A F n)
    (subgroupEigenbasisMicrostate A F n g)

omit [F.Normal] in
theorem norm_subgroupCornerMicrostate_le_one (n : ℕ) (g : E) :
    ‖subgroupCornerMicrostate A F n g‖ ≤ 1 := by
  exact (norm_principalBlock_le (subgroupCornerPredicate A F n)
    (subgroupEigenbasisMicrostate A F n g)).trans_eq
      (norm_subgroupEigenbasisMicrostate_eq_one A F n g)

/-- The rounded projection asymptotically commutes with every ambient
microstate. -/
theorem subgroupProjection_commutator_vanishing (g : E) :
    OpNormVanishing A (fun n ↦
      subgroupProjection A F n *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          subgroupProjection A F n) := by
  have hconj := subgroupProjection_conjugation_vanishing A F g
  have hright (n : ℕ) :
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ ≤ 1 :=
    norm_le_one_of_mem_unitary (A.map n g).2
  have hmul := hconj.mul_right_of_norm_le_one
    (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ)) hright
  refine hmul.neg.congr fun n ↦ ?_
  let U : Matrix (A.model n) (A.model n) ℂ := A.map n g
  let P : Matrix (A.model n) (A.model n) ℂ := subgroupProjection A F n
  have hstar :
      Uᴴ * U = 1 := by
    have hu := (A.map n g).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    simpa [U] using hu
  change -((U * P * Uᴴ - P) * U) = P * U - U * P
  rw [Matrix.sub_mul, Matrix.mul_assoc, hstar, Matrix.mul_one]
  module

/- In the selected eigenbasis, the rounded projection is the diagonal
indicator of the complementary predicate's complement. -/
omit [F.Normal] in
theorem eigenbasis_subgroupProjection_eq_diagonal (n : ℕ) :
    let hH := hermitianSubgroupAverage_isHermitian A F n
    let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
    Vᴴ * subgroupProjection A F n * V =
      Matrix.diagonal (fun i ↦
        if ¬subgroupCornerPredicate A F n i then (1 : ℂ) else 0) := by
  let hH := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  let D : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦ if (1 / 2 : ℝ) < hH.eigenvalues i then 1 else 0)
  have hVV : Vᴴ * V = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hD : D = Matrix.diagonal (fun i ↦
      if ¬subgroupCornerPredicate A F n i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [D, Matrix.diagonal_apply_eq]
      change (if (1 / 2 : ℝ) < hH.eigenvalues i then (1 : ℂ) else 0) =
        if ¬hH.eigenvalues i ≤ (1 / 2 : ℝ) then (1 : ℂ) else 0
      simp only [not_le]
    · simp [D, hij]
  change Vᴴ * (V * D * Vᴴ) * V = _
  rw [show Vᴴ * (V * D * Vᴴ) * V =
      (Vᴴ * V) * D * (Vᴴ * V) by noncomm_ring,
    hVV, Matrix.one_mul, Matrix.mul_one, hD]

/-- The eigenbasis projection commutator controls both off-diagonal blocks
with constant one. -/
theorem offDiagonalBlocks_eventually_small (g : E) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖coordinateBlock (subgroupCornerPredicate A F n)
          (fun i ↦ ¬subgroupCornerPredicate A F n i)
          (subgroupEigenbasisMicrostate A F n g)‖ ≤ eta ∧
      ‖coordinateBlock (fun i ↦ ¬subgroupCornerPredicate A F n i)
          (subgroupCornerPredicate A F n)
          (subgroupEigenbasisMicrostate A F n g)‖ ≤ eta := by
  intro eta heta
  obtain ⟨N, hN⟩ := subgroupProjection_commutator_vanishing A F g eta heta
  refine ⟨N, fun n hn ↦ ?_⟩
  let hH := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  let D : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦
      if ¬subgroupCornerPredicate A F n i then (1 : ℂ) else 0)
  let W := subgroupEigenbasisMicrostate A F n g
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hcommEq : D * W - W * D =
      Vᴴ * (subgroupProjection A F n *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          subgroupProjection A F n) * V := by
    have hD := eigenbasis_subgroupProjection_eq_diagonal A F n
    dsimp only at hD
    have hD' : D = Vᴴ * subgroupProjection A F n * V := by
      symm
      exact hD
    rw [hD']
    simp only [W, subgroupEigenbasisMicrostate]
    have hVV : V * Vᴴ = 1 :=
      Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
    rw [show
      (Vᴴ * subgroupProjection A F n * V) *
          (Vᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * V) -
        (Vᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * V) *
          (Vᴴ * subgroupProjection A F n * V) =
        Vᴴ * (subgroupProjection A F n * (V * Vᴴ) * A.map n g -
          A.map n g * (V * Vᴴ) * subgroupProjection A F n) * V by
            noncomm_ring,
      hVV]
    simp only [Matrix.mul_one]
  have hcomm : ‖D * W - W * D‖ ≤ eta := by
    calc
      ‖D * W - W * D‖ =
          ‖subgroupProjection A F n *
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              subgroupProjection A F n‖ := by
        rw [hcommEq]
        simpa only [Matrix.conjTranspose_conjTranspose] using
          norm_unitary_conjugate hVstar
            (D := subgroupProjection A F n *
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              subgroupProjection A F n)
      _ ≤ eta := hN n hn
  constructor
  · have hb := norm_coordinateBlock_le (subgroupCornerPredicate A F n)
      (fun i ↦ ¬subgroupCornerPredicate A F n i) (D * W - W * D)
    have heq : coordinateBlock (subgroupCornerPredicate A F n)
        (fun i ↦ ¬subgroupCornerPredicate A F n i) (D * W - W * D) =
      -coordinateBlock (subgroupCornerPredicate A F n)
        (fun i ↦ ¬subgroupCornerPredicate A F n i) W := by
      ext i j
      simp [D, coordinateBlock, Matrix.toBlock_apply, i.2, j.2]
    rw [heq, norm_neg] at hb
    exact hb.trans hcomm
  · have hb := norm_coordinateBlock_le
      (fun i ↦ ¬subgroupCornerPredicate A F n i)
      (subgroupCornerPredicate A F n) (D * W - W * D)
    have heq : coordinateBlock
        (fun i ↦ ¬subgroupCornerPredicate A F n i)
        (subgroupCornerPredicate A F n) (D * W - W * D) =
      coordinateBlock (fun i ↦ ¬subgroupCornerPredicate A F n i)
        (subgroupCornerPredicate A F n) W := by
      ext i j
      simp [D, coordinateBlock, Matrix.toBlock_apply, i.2, j.2]
    rw [heq] at hb
    exact hb.trans hcomm

/-- Multiplication defects of the uncorrected complementary corner vanish
in operator norm. -/
theorem subgroupCornerMicrostate_multiplicative_eventually (g h : E) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖subgroupCornerMicrostate A F n (g * h) -
        subgroupCornerMicrostate A F n g *
          subgroupCornerMicrostate A F n h‖ ≤ eta := by
  intro eta heta
  obtain ⟨Nm, hNm⟩ := A.asymptoticallyMultiplicative g h
    (eta / 2) (by linarith)
  obtain ⟨No, hNo⟩ := offDiagonalBlocks_eventually_small A F g
    (eta / 2) (by linarith)
  refine ⟨max Nm No, fun n hn ↦ ?_⟩
  have hright : ‖coordinateBlock
      (fun i ↦ ¬subgroupCornerPredicate A F n i)
      (subgroupCornerPredicate A F n)
      (subgroupEigenbasisMicrostate A F n h)‖ ≤ 1 :=
    (norm_coordinateBlock_le _ _ _).trans_eq
      (norm_subgroupEigenbasisMicrostate_eq_one A F n h)
  calc
    ‖subgroupCornerMicrostate A F n (g * h) -
        subgroupCornerMicrostate A F n g *
          subgroupCornerMicrostate A F n h‖ ≤
      ‖subgroupEigenbasisMicrostate A F n (g * h) -
        subgroupEigenbasisMicrostate A F n g *
          subgroupEigenbasisMicrostate A F n h‖ +
      ‖coordinateBlock (subgroupCornerPredicate A F n)
          (fun i ↦ ¬subgroupCornerPredicate A F n i)
          (subgroupEigenbasisMicrostate A F n g)‖ *
      ‖coordinateBlock (fun i ↦ ¬subgroupCornerPredicate A F n i)
          (subgroupCornerPredicate A F n)
          (subgroupEigenbasisMicrostate A F n h)‖ :=
      norm_principalBlock_mul_defect_le _ _ _ _
    _ = ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ +
        ‖coordinateBlock (subgroupCornerPredicate A F n)
          (fun i ↦ ¬subgroupCornerPredicate A F n i)
          (subgroupEigenbasisMicrostate A F n g)‖ *
        ‖coordinateBlock (fun i ↦ ¬subgroupCornerPredicate A F n i)
          (subgroupCornerPredicate A F n)
          (subgroupEigenbasisMicrostate A F n h)‖ := by
      rw [norm_subgroupEigenbasisMicrostate_mul_defect_eq]
    _ ≤ eta / 2 + (eta / 2) * 1 := add_le_add
      (hNm n ((le_max_left _ _).trans hn))
      (mul_le_mul (hNo n ((le_max_right _ _).trans hn)).1 hright
        (norm_nonneg _) (by linarith))
    _ = eta := by ring

/-- Gram defects of the uncorrected complementary corner vanish in
operator norm. -/
theorem subgroupCornerMicrostate_gram_eventually (g : E) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖cornerGram (subgroupCornerMicrostate A F n g) - 1‖ ≤ eta := by
  intro eta heta
  obtain ⟨N, hN⟩ := offDiagonalBlocks_eventually_small A F g
    (Real.sqrt eta) (Real.sqrt_pos.2 heta)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hunit :
      (subgroupEigenbasisMicrostate A F n g)ᴴ *
          subgroupEigenbasisMicrostate A F n g = 1 := by
    have hu := subgroupEigenbasisMicrostate_mem_unitaryGroup A F n g
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
    exact hu
  have hgram := norm_principalBlock_gram_sub_one_le
    (subgroupCornerPredicate A F n)
    (subgroupEigenbasisMicrostate A F n g) hunit
  refine hgram.trans ?_
  have hb := (hN n hn).2
  nlinarith [norm_nonneg (coordinateBlock
    (fun i ↦ ¬subgroupCornerPredicate A F n i)
    (subgroupCornerPredicate A F n)
    (subgroupEigenbasisMicrostate A F n g)), Real.sq_sqrt heta.le]

/-- Exact unitary obtained by polar correction of a good complementary
corner compression, and the identity outside the certified branch. -/
noncomputable def subgroupCornerUnitary (n : ℕ) (g : E) :
    Matrix.unitaryGroup (subgroupCornerModel A F n) ℂ :=
  if hclose : ‖cornerGram (subgroupCornerMicrostate A F n g) - 1‖ ≤ 1 / 2 then
    polarCorrectUnitary (subgroupCornerMicrostate A F n g)
      (cornerGram_isHermitian _) le_rfl hclose
  else 1

/-- Polar correction is asymptotically invisible. -/
theorem subgroupCornerUnitary_close_eventually (g : E) :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖(subgroupCornerUnitary A F n g :
          Matrix (subgroupCornerModel A F n)
            (subgroupCornerModel A F n) ℂ) -
        subgroupCornerMicrostate A F n g‖ ≤ eta := by
  intro eta heta
  obtain ⟨N, hN⟩ := subgroupCornerMicrostate_gram_eventually A F g
    (min (eta / 2) (1 / 2)) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hclose : ‖cornerGram (subgroupCornerMicrostate A F n g) - 1‖ ≤
      1 / 2 := (hN n hn).trans (min_le_right _ _)
  simp only [subgroupCornerUnitary]
  rw [dif_pos hclose]
  have hb := norm_polarCorrect_sub_le (subgroupCornerMicrostate A F n g)
    (cornerGram_isHermitian _) (norm_subgroupCornerMicrostate_le_one A F n g)
    (show 0 ≤ min (eta / 2) (1 / 2) by positivity)
    (min_le_right _ _) (hN n hn)
  calc
    ‖(polarCorrectUnitary (subgroupCornerMicrostate A F n g)
          (cornerGram_isHermitian _) le_rfl hclose :
        Matrix (subgroupCornerModel A F n)
          (subgroupCornerModel A F n) ℂ) -
      subgroupCornerMicrostate A F n g‖ ≤
        2 * min (eta / 2) (1 / 2) := hb
    _ ≤ 2 * (eta / 2) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    _ = eta := by ring

/- A nonzero complementary projection yields a low-eigenvalue coordinate. -/
omit [F.Normal] in
theorem nonempty_subgroupCornerModel_of_complement_ne_zero (n : ℕ)
    (hne : subgroupComplementProjection A F n ≠ 0) :
    Nonempty (subgroupCornerModel A F n) := by
  by_contra hempty
  have hall : ∀ i : A.model n,
      (1 / 2 : ℝ) <
        (hermitianSubgroupAverage_isHermitian A F n).eigenvalues i := by
    intro i
    exact lt_of_not_ge fun hi ↦ hempty ⟨⟨i, hi⟩⟩
  have hP : subgroupProjection A F n = 1 :=
    spectralAbove_eq_one_of_forall_lt _ _ _ hall
  apply hne
  simp [subgroupComplementProjection, hP]

/- The normalized finite-group average of the uncorrected corner
microstates is exactly the low principal block of the conjugated Reynolds
average. -/
omit [F.Normal] in
theorem normalized_sum_subgroupCornerMicrostate_eq (n : ℕ) :
    ((Fintype.card F : ℂ)⁻¹) •
        ∑ f : F, subgroupCornerMicrostate A F n (f : E) =
      let hH := hermitianSubgroupAverage_isHermitian A F n
      let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
      principalBlock (subgroupCornerPredicate A F n)
        (Vᴴ * subgroupAverage A F n * V) := by
  let hH := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  change ((Fintype.card F : ℂ)⁻¹) •
      ∑ f : F, principalBlock (subgroupCornerPredicate A F n)
        (subgroupEigenbasisMicrostate A F n (f : E)) =
    principalBlock (subgroupCornerPredicate A F n)
      (Vᴴ * subgroupAverage A F n * V)
  have hinside : ((Fintype.card F : ℂ)⁻¹) •
      ∑ f : F, subgroupEigenbasisMicrostate A F n (f : E) =
        Vᴴ * subgroupAverage A F n * V := by
    change ((Fintype.card F : ℂ)⁻¹) •
        ∑ f : F, Vᴴ *
          (A.map n (f : E) : Matrix (A.model n) (A.model n) ℂ) * V =
      Vᴴ * (((Fintype.card F : ℂ)⁻¹) •
        ∑ f : F, (A.map n (f : E) :
          Matrix (A.model n) (A.model n) ℂ)) * V
    rw [Matrix.mul_smul, Matrix.smul_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← hinside]
  ext i j
  simp only [principalBlock, coordinateBlock, Matrix.toBlock_apply,
    Matrix.smul_apply, Matrix.sum_apply]

/- The finite-group sum of uncorrected corner microstates vanishes in
operator norm. -/
omit [F.Normal] in
theorem subgroupCornerMicrostate_sum_eventually :
    ∀ eta : ℝ, 0 < eta → ∃ N, ∀ n ≥ N,
      ‖∑ f : F, subgroupCornerMicrostate A F n (f : E)‖ ≤ eta := by
  intro eta heta
  have hcardNat : 0 < Fintype.card F := Fintype.card_pos
  have hcardReal : (0 : ℝ) < Fintype.card F := by exact_mod_cast hcardNat
  obtain ⟨N, hN⟩ := subgroupProjection_sub_average_vanishing A F
    (eta / Fintype.card F) (div_pos heta hcardReal)
  refine ⟨N, fun n hn ↦ ?_⟩
  let hH := hermitianSubgroupAverage_isHermitian A F n
  let V : Matrix (A.model n) (A.model n) ℂ := hH.eigenvectorUnitary
  let p := subgroupCornerPredicate A F n
  let C := ∑ f : F, subgroupCornerMicrostate A F n (f : E)
  let R := principalBlock p (Vᴴ * subgroupAverage A F n * V)
  have havg : ((Fintype.card F : ℂ)⁻¹) • C = R := by
    simpa [C, R, p, hH, V] using
      normalized_sum_subgroupCornerMicrostate_eq A F n
  have hcardC : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hC : C = (Fintype.card F : ℂ) • R := by
    have h := congrArg (fun M ↦ (Fintype.card F : ℂ) • M) havg
    simpa [smul_smul, hcardC] using h
  have hPzero : principalBlock p (Vᴴ * subgroupProjection A F n * V) = 0 := by
    have hdiag := eigenbasis_subgroupProjection_eq_diagonal A F n
    dsimp only at hdiag
    change Vᴴ * subgroupProjection A F n * V = _ at hdiag
    rw [hdiag]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [p, principalBlock, coordinateBlock, Matrix.toBlock_apply,
        i.property]
    · have hne : (i : A.model n) ≠ (j : A.model n) :=
        fun h ↦ hij (Subtype.ext h)
      change Matrix.diagonal
        (fun k ↦ if ¬subgroupCornerPredicate A F n k then (1 : ℂ) else 0)
          (i : A.model n) (j : A.model n) = 0
      rw [Matrix.diagonal_apply_ne _ hne]
  have hR : ‖R‖ ≤
      ‖subgroupAverage A F n - subgroupProjection A F n‖ := by
    have hVstar : Vᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have heq : R = principalBlock p
        (Vᴴ * (subgroupAverage A F n - subgroupProjection A F n) * V) := by
      change principalBlock p (Vᴴ * subgroupAverage A F n * V) = _
      rw [show Vᴴ * (subgroupAverage A F n - subgroupProjection A F n) * V =
        Vᴴ * subgroupAverage A F n * V -
          Vᴴ * subgroupProjection A F n * V by noncomm_ring,
        principalBlock_sub, hPzero, sub_zero]
    rw [heq]
    exact (norm_principalBlock_le p _).trans_eq (by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        norm_unitary_conjugate hVstar
          (D := subgroupAverage A F n - subgroupProjection A F n))
  change ‖C‖ ≤ eta
  rw [hC, norm_smul, Complex.norm_natCast]
  calc
    (Fintype.card F : ℝ) * ‖R‖ ≤
        (Fintype.card F : ℝ) *
          ‖subgroupAverage A F n - subgroupProjection A F n‖ :=
      mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
    _ ≤ (Fintype.card F : ℝ) * (eta / Fintype.card F) := by
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_left (hN n hn) (Nat.cast_nonneg _)
    _ = eta := by field_simp

end CornerMatrices

/-! ## Packaged complementary corner -/

section CornerPackaging

variable (A : OpAlmostRepresentation E) (F : Subgroup E)
  [Fintype F] [F.Normal]

/-- Package the eventually nonempty complementary averaging corner as an
operator-norm almost representation. -/
noncomputable def subgroupCornerAlmostRepresentation (N₀ : ℕ)
    (hN₀ : ∀ n ≥ N₀, Nonempty (subgroupCornerModel A F n)) :
    OpAlmostRepresentation E where
  model n := subgroupCornerModel A F (max n N₀)
  modelNonempty n := Fintype.card_pos_iff.mpr
    (hN₀ _ (le_max_right n N₀))
  map n g := subgroupCornerUnitary A F (max n N₀) g
  asymptoticallyMultiplicative := by
    intro g h eta heta
    obtain ⟨Nm, hNm⟩ := subgroupCornerMicrostate_multiplicative_eventually
      A F g h (eta / 4) (by linarith)
    obtain ⟨Ng, hNg⟩ := subgroupCornerUnitary_close_eventually
      A F g (eta / 4) (by linarith)
    obtain ⟨Nh, hNh⟩ := subgroupCornerUnitary_close_eventually
      A F h (eta / 4) (by linarith)
    obtain ⟨Ngh, hNgh⟩ := subgroupCornerUnitary_close_eventually
      A F (g * h) (eta / 4) (by linarith)
    refine ⟨max (max Nm Ng) (max Nh Ngh), fun n hn ↦ ?_⟩
    have hm : Nm ≤ max n N₀ := le_trans
      ((le_max_left Nm Ng).trans ((le_max_left _ _).trans hn))
      (le_max_left n N₀)
    have hg : Ng ≤ max n N₀ := le_trans
      ((le_max_right Nm Ng).trans ((le_max_left _ _).trans hn))
      (le_max_left n N₀)
    have hh : Nh ≤ max n N₀ := le_trans
      ((le_max_left Nh Ngh).trans ((le_max_right _ _).trans hn))
      (le_max_left n N₀)
    have hgh : Ngh ≤ max n N₀ := le_trans
      ((le_max_right Nh Ngh).trans ((le_max_right _ _).trans hn))
      (le_max_left n N₀)
    exact norm_mul_defect_le_of_close
      (subgroupCornerMicrostate A F (max n N₀) g)
      (subgroupCornerMicrostate A F (max n N₀) h)
      (subgroupCornerMicrostate A F (max n N₀) (g * h))
      (subgroupCornerUnitary A F (max n N₀) g)
      (subgroupCornerUnitary A F (max n N₀) h)
      (subgroupCornerUnitary A F (max n N₀) (g * h))
      (hNgh _ hgh) (hNm _ hm) (hNg _ hg) (hNh _ hh)
      (norm_le_one_of_mem_unitaryGroup
        (subgroupCornerUnitary A F (max n N₀) h).2)
      (norm_subgroupCornerMicrostate_le_one A F (max n N₀) g)

@[simp] theorem subgroupCornerAlmostRepresentation_map (N₀ : ℕ)
    (hN₀ : ∀ n ≥ N₀, Nonempty (subgroupCornerModel A F n))
    (n : ℕ) (g : E) :
    (subgroupCornerAlmostRepresentation A F N₀ hN₀).map n g =
      subgroupCornerUnitary A F (max n N₀) g := rfl

/-- After packaging and polar correction, the unnormalized finite-group sum
still vanishes in operator norm. -/
theorem subgroupCornerAlmostRepresentation_sum_vanishing (N₀ : ℕ)
    (hN₀ : ∀ n ≥ N₀, Nonempty (subgroupCornerModel A F n)) :
    let B := subgroupCornerAlmostRepresentation A F N₀ hN₀
    OpNormVanishing B (fun n ↦
      ∑ f : F, (B.map n (f : E) :
        Matrix (B.model n) (B.model n) ℂ)) := by
  dsimp only
  intro eta heta
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  obtain ⟨Ns, hNs⟩ := subgroupCornerMicrostate_sum_eventually A F
    (eta / 2) (by linarith)
  have hcloseEach : ∀ f : F, ∃ N, ∀ n ≥ N,
      ‖(subgroupCornerUnitary A F n (f : E) :
          Matrix (subgroupCornerModel A F n)
            (subgroupCornerModel A F n) ℂ) -
        subgroupCornerMicrostate A F n (f : E)‖ ≤
          eta / (2 * Fintype.card F) := by
    intro f
    exact subgroupCornerUnitary_close_eventually A F (f : E)
      (eta / (2 * Fintype.card F)) (div_pos heta (by positivity))
  choose Nc hNc using hcloseEach
  let Nclose := Finset.univ.sup Nc
  have hNcAll (n : ℕ) (hn : Nclose ≤ n) (f : F) :
      ‖(subgroupCornerUnitary A F n (f : E) :
          Matrix (subgroupCornerModel A F n)
            (subgroupCornerModel A F n) ℂ) -
        subgroupCornerMicrostate A F n (f : E)‖ ≤
          eta / (2 * Fintype.card F) := by
    apply hNc f n
    exact (Finset.le_sup (s := Finset.univ) (f := Nc)
      (Finset.mem_univ f)).trans hn
  refine ⟨max Ns Nclose, fun n hn ↦ ?_⟩
  have hs : Ns ≤ max n N₀ :=
    (le_max_left Ns Nclose).trans hn |>.trans (le_max_left n N₀)
  have hc : Nclose ≤ max n N₀ :=
    (le_max_right Ns Nclose).trans hn |>.trans (le_max_left n N₀)
  change ‖∑ f : F,
      (subgroupCornerUnitary A F (max n N₀) (f : E) :
        Matrix (subgroupCornerModel A F (max n N₀))
          (subgroupCornerModel A F (max n N₀)) ℂ)‖ ≤ eta
  have hsplit :
      (∑ f : F,
        (subgroupCornerUnitary A F (max n N₀) (f : E) :
          Matrix (subgroupCornerModel A F (max n N₀))
            (subgroupCornerModel A F (max n N₀)) ℂ)) =
      (∑ f : F,
        ((subgroupCornerUnitary A F (max n N₀) (f : E) :
            Matrix (subgroupCornerModel A F (max n N₀))
              (subgroupCornerModel A F (max n N₀)) ℂ) -
          subgroupCornerMicrostate A F (max n N₀) (f : E))) +
      ∑ f : F, subgroupCornerMicrostate A F (max n N₀) (f : E) := by
    simp only [Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  calc
    ‖(∑ f : F,
        ((subgroupCornerUnitary A F (max n N₀) (f : E) :
            Matrix (subgroupCornerModel A F (max n N₀))
              (subgroupCornerModel A F (max n N₀)) ℂ) -
          subgroupCornerMicrostate A F (max n N₀) (f : E))) +
      ∑ f : F, subgroupCornerMicrostate A F (max n N₀) (f : E)‖ ≤
        ‖∑ f : F,
          ((subgroupCornerUnitary A F (max n N₀) (f : E) :
              Matrix (subgroupCornerModel A F (max n N₀))
                (subgroupCornerModel A F (max n N₀)) ℂ) -
            subgroupCornerMicrostate A F (max n N₀) (f : E))‖ +
        ‖∑ f : F, subgroupCornerMicrostate A F (max n N₀) (f : E)‖ :=
      norm_add_le _ _
    _ ≤ (∑ f : F,
        ‖(subgroupCornerUnitary A F (max n N₀) (f : E) :
            Matrix (subgroupCornerModel A F (max n N₀))
              (subgroupCornerModel A F (max n N₀)) ℂ) -
          subgroupCornerMicrostate A F (max n N₀) (f : E)‖) + eta / 2 :=
      add_le_add (norm_sum_le _ _) (hNs _ hs)
    _ ≤ (∑ _f : F, eta / (2 * Fintype.card F)) + eta / 2 :=
      add_le_add (Finset.sum_le_sum fun f _ ↦ hNcAll _ hc f) le_rfl
    _ = eta := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      norm_num

end CornerPackaging

/-! ## The finite-average Hilbert--Schmidt contradiction -/

section FiniteAverageContradiction

variable (B : OpAlmostRepresentation E) (F : Subgroup E) [Fintype F]

/-- Eventual normalized Hilbert--Schmidt coincidence of two fixed group
microstates. -/
def HSDistVanishing (g h : E) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
    hsDistSq (B.model n) (B.map n g) (B.map n h) ≤ epsilon

/-- Hilbert--Schmidt closeness controls normalized traces. -/
theorem norm_normTrace_sub_le_sqrt_hsDistSq (n : ℕ) (g h : E) :
    ‖normTrace (B.model n) (B.map n g) -
        normTrace (B.model n) (B.map n h)‖ ≤
      Real.sqrt (hsDistSq (B.model n) (B.map n g) (B.map n h)) := by
  rw [← normTrace_sub]
  exact norm_normTrace_le_hsNorm _ _

/-- If a finite family of unitary microstates all become Hilbert--Schmidt
equal to the identity microstate, their unnormalized sum cannot converge to
zero in operator norm. -/
theorem false_of_finite_sum_vanishing_of_hsTrivial
    (hsum : OpNormVanishing B (fun n ↦
      ∑ f : F, (B.map n (f : E) :
        Matrix (B.model n) (B.model n) ℂ)))
    (hclose : ∀ f : F, HSDistVanishing B (f : E) 1) : False := by
  classical
  let m : ℝ := Fintype.card F
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let delta : ℝ := 1 / (8 * m)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨Ns, hNs⟩ := hsum (1 / 8) (by norm_num)
  obtain ⟨N1, hN1⟩ := map_one_vanishing B delta hdelta
  have hcloseEach : ∀ f : F, ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n) (B.map n (f : E)) (B.map n 1) ≤ delta ^ 2 := by
    intro f
    exact hclose f (delta ^ 2) (sq_pos_of_pos hdelta)
  choose Nc hNc using hcloseEach
  let Nclose := Finset.univ.sup Nc
  let n := max (max Ns N1) Nclose
  have hns : Ns ≤ n := (le_max_left Ns N1).trans (le_max_left _ _)
  have hn1 : N1 ≤ n := (le_max_right Ns N1).trans (le_max_left _ _)
  have hnc (f : F) : Nc f ≤ n :=
    (Finset.le_sup (s := Finset.univ) (f := Nc) (Finset.mem_univ f)).trans
      (le_max_right _ _)
  let Y := B.model n
  let U1 : Matrix Y Y ℂ := B.map n 1
  let T : Matrix Y Y ℂ := ∑ f : F, (B.map n (f : E) : Matrix Y Y ℂ)
  let tau1 : ℂ := normTrace Y U1
  let tauT : ℂ := normTrace Y T
  have htraceClose (f : F) :
      ‖normTrace Y (B.map n (f : E)) - tau1‖ ≤ delta := by
    have htr := norm_normTrace_sub_le_sqrt_hsDistSq B n (f : E) 1
    have hsq := hNc f n (hnc f)
    have hsqrt : Real.sqrt
        (hsDistSq Y (B.map n (f : E)) (B.map n 1)) ≤ delta := by
      calc
        Real.sqrt (hsDistSq Y (B.map n (f : E)) (B.map n 1)) ≤
            Real.sqrt (delta ^ 2) := Real.sqrt_le_sqrt hsq
        _ = delta := Real.sqrt_sq hdelta.le
    exact htr.trans hsqrt
  have htau1 : ‖tau1 - 1‖ ≤ delta := by
    have hop : ‖U1 - 1‖ ≤ delta := by simpa [U1] using hN1 n hn1
    have hY : 0 < Fintype.card Y := B.modelNonempty n
    have htrace : normTrace Y (U1 - 1) = tau1 - 1 := by
      rw [normTrace_sub, normTrace_one' Y hY]
    rw [← htrace]
    exact (norm_normTrace_le_l2_opNorm Y hY (U1 - 1)).trans hop
  have htauT : ‖tauT‖ ≤ 1 / 8 := by
    have hY : 0 < Fintype.card Y := B.modelNonempty n
    exact (norm_normTrace_le_l2_opNorm Y hY T).trans
      (by simpa [T] using hNs n hns)
  have htauSum : tauT = ∑ f : F, normTrace Y (B.map n (f : E)) := by
    simp only [tauT, T, normTrace, Matrix.trace_sum, Finset.sum_div]
  have hfirst : ‖tauT - (Fintype.card F : ℂ) * tau1‖ ≤ 1 / 8 := by
    have heq : tauT - (Fintype.card F : ℂ) * tau1 =
        ∑ f : F, (normTrace Y (B.map n (f : E)) - tau1) := by
      rw [htauSum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [heq]
    calc
      ‖∑ f : F, (normTrace Y (B.map n (f : E)) - tau1)‖ ≤
          ∑ f : F, ‖normTrace Y (B.map n (f : E)) - tau1‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _f : F, delta := Finset.sum_le_sum fun f _ ↦ htraceClose f
      _ = m * delta := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 1 / 8 := by dsimp [delta]; field_simp
  have hsecond : ‖(Fintype.card F : ℂ) * tau1 -
      (Fintype.card F : ℂ)‖ ≤ 1 / 8 := by
    rw [show (Fintype.card F : ℂ) * tau1 - (Fintype.card F : ℂ) =
      (Fintype.card F : ℂ) * (tau1 - 1) by ring, norm_mul,
      Complex.norm_natCast]
    calc
      (Fintype.card F : ℝ) * ‖tau1 - 1‖ ≤ m * delta :=
        mul_le_mul_of_nonneg_left htau1 (Nat.cast_nonneg _)
      _ = 1 / 8 := by dsimp [delta]; field_simp
  have hbound : ‖(Fintype.card F : ℂ)‖ ≤ 3 / 8 := by
    have heq : (Fintype.card F : ℂ) =
        ((Fintype.card F : ℂ) - (Fintype.card F : ℂ) * tau1) +
          (((Fintype.card F : ℂ) * tau1 - tauT) + tauT) := by ring
    rw [heq]
    calc
      ‖((Fintype.card F : ℂ) - (Fintype.card F : ℂ) * tau1) +
          (((Fintype.card F : ℂ) * tau1 - tauT) + tauT)‖ ≤
        ‖(Fintype.card F : ℂ) - (Fintype.card F : ℂ) * tau1‖ +
          (‖(Fintype.card F : ℂ) * tau1 - tauT‖ + ‖tauT‖) := by
        exact (norm_add_le _ _).trans
          (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ 1 / 8 + (1 / 8 + 1 / 8) := by
        rw [norm_sub_rev, norm_sub_rev]
        exact add_le_add (by simpa [norm_sub_rev] using hsecond)
          (add_le_add (by simpa [norm_sub_rev] using hfirst) htauT)
      _ = 3 / 8 := by ring
  rw [Complex.norm_natCast] at hbound
  have : m ≤ 3 / 8 := by simpa [m] using hbound
  linarith

end FiniteAverageContradiction

/-! ## Arbitrary-ultrafilter adapter -/

/-- **Coordinate finite-normal corner adapter.**

Starting from the Hermitianized finite-subgroup averages, round at spectral
threshold `1/2`, retain the complementary nonzero coordinates selected by a
surviving finite-subgroup image, and polar-correct the compressed ambient
microstates.  The resulting operator-norm almost representation has vanishing
finite-group sum.

This is the coordinatewise replacement for the additive corona proof of
Lemma `finite-normal corners` in the manuscript.  It is intentionally stated
separately from the Kazhdan argument. -/
theorem exists_corner_with_finite_sum_vanishing
    [Countable E] (F : Subgroup E) [Finite F] [F.Normal]
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : E →* UniversalWeakMF U X)
    (hnontrivial : ∃ f : F, rho f ≠ 1) :
    ∃ B : OpAlmostRepresentation E,
      letI : Fintype F := Fintype.ofFinite F
      OpNormVanishing B (fun n ↦
        ∑ f : F, (B.map n (f : E) :
          Matrix (B.model n) (B.model n) ℂ)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hf⟩ := hnontrivial
  obtain ⟨A⟩ := exists_markedOpAlmostRepresentation_of_ne_one
    U X rho hf
  obtain ⟨N₀, hN₀⟩ :=
    subgroupComplementProjection_eventually_ne_zero F f A
  have hcorner : ∀ n ≥ N₀,
      Nonempty (subgroupCornerModel A.toOpAlmostRepresentation F n) := by
    intro n hn
    exact nonempty_subgroupCornerModel_of_complement_ne_zero
      A.toOpAlmostRepresentation F n (hN₀ n hn)
  refine ⟨subgroupCornerAlmostRepresentation
    A.toOpAlmostRepresentation F N₀ hcorner, ?_⟩
  exact subgroupCornerAlmostRepresentation_sum_vanishing
    A.toOpAlmostRepresentation F N₀ hcorner

end FiniteNormalAverageCorner
end GroupApproximation
