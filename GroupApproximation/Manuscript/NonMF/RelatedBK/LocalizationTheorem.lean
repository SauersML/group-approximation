import GroupApproximation.Manuscript.NonMF.RelatedBK.LocalizationSupport
import GroupApproximation.Manuscript.NonMF.RelatedBK.Sentence
import GroupApproximation.Analysis.FiniteMatrixBlockCPRetract
import GroupApproximation.Analysis.FiniteDirectSumMatrixCPRetract
import GroupApproximation.Analysis.FiniteDimensionalCStarMatrixCPRetract
import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalLift
import GroupApproximation.Analysis.BlackadarKirchbergFiniteCoordinateUCP
import GroupApproximation.Analysis.BlackadarKirchbergConvexSupportDensity
import GroupApproximation.Analysis.OperatorNormCertificate
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): the finite-coordinate localization theorem

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

This module proves `CoronaUCPFiniteCoordinateLocalizationStatement` and closes the printed
equivalence as `manuscriptSentence_blackadarKirchbergNFIff`.

## Proof route

Let `Ext : Q(X) → D` be UCP, `T` finite, `δ > 0` and `N` given.

1. Embed `D` into a full matrix algebra `M_Z` with a UCP retract `E`
   (`exists_matrixUCPRetract_of_finiteDimensionalCStar`). The map
   `Φ = ι ∘ Ext ∘ mk : ∏ M_{X n} → M_Z` is UCP, contractive, and kills every sequence
   vanishing at the coordinates `n ≥ N`.
2. Put `T' = T ∪ {1}`. By `localization_support` and the convex support criterion
   `exists_convexHull_near_of_approximate_complex_support`, the point `(i, j, t) ↦ Φ(t)_{ij}`
   is within `ε` (sup norm) of a finite convex combination `∑_κ w_κ z_κ` of vector states
   `z_κ` at coordinates `m κ ≥ N`, given by vectors `ξ_κ : Z × X (m κ) → ℂ`.
3. Put `Y = Σ_κ X (m κ)` and `ρ x = ⊕_κ x (m κ)`. This is a star homomorphism and only sees
   coordinates `≥ N`.
4. Let `s = (1 + K ε)⁻¹` with `K = |Z|²`, and let `Ψ : M_Y → M_Z` be the row-Gram Choi map of
   the rows `V ⟨κ, a⟩ = √(s w_κ) ξ_κ(·, a)`. Then `Ψ` is CP and
   `Ψ(ρ x)_{ij} = s ∑_κ w_κ z_κ(i, j, x)`, so the entries of `Ψ(ρ x) - s Φ x` are at most
   `s ε` on `T'`. At `x = 1` this gives `‖Ψ 1‖ ≤ s (1 + K ε) = 1`, so `Ψ` is contractive.
5. Take `θ = E ∘ Ψ`. For `x ∈ T`, `‖θ (ρ x) - Ext (mk x)‖ ≤ ‖Ψ(ρ x) - Φ x‖
   ≤ K (ε + (1 - s) ‖x‖) ≤ δ` for the choice `ε = δ / (1 + K (1 + K C))`,
   `C = ∑_{t ∈ T} ‖t‖`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBK

open GroupApproximation.CStarExactness
open scoped Matrix Matrix.Norms.L2Operator

universe u

noncomputable section

/-- Bounded matrix sequences form a C-star algebra. -/
local instance boundedMatrixSequenceCStarAlgebraForLocalizationTheorem
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarAlgebra (BoundedMatrixSequence (fun n ↦ X n)) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForLocalizationTheorem
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The block-diagonal star homomorphism `x ↦ ⊕_κ x (m κ)`. -/
def localizationRho (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {ι : Type} [Fintype ι]
    [DecidableEq ι] (m : ι → ℕ) :
    BoundedMatrixSequence (fun n ↦ X n) →⋆ₙₐ[ℂ] Matrix (Σ κ, X (m κ)) (Σ κ, X (m κ)) ℂ where
  toFun x := Matrix.blockDiagonal' fun κ ↦ x (m κ)
  map_smul' c x := by
    change Matrix.blockDiagonal' (c • fun κ ↦ x (m κ)) = c • Matrix.blockDiagonal' fun κ ↦ x (m κ)
    exact Matrix.blockDiagonal'_smul c fun κ ↦ x (m κ)
  map_zero' := by
    change Matrix.blockDiagonal'
      (fun κ ↦ (0 : BoundedMatrixSequence (fun n ↦ X n)) (m κ)) = 0
    exact Matrix.blockDiagonal'_zero
  map_add' x y := Matrix.blockDiagonal'_add (fun κ ↦ x (m κ)) (fun κ ↦ y (m κ))
  map_mul' x y := Matrix.blockDiagonal'_mul (fun κ ↦ x (m κ)) (fun κ ↦ y (m κ))
  map_star' x := (Matrix.blockDiagonal'_conjTranspose (fun κ ↦ x (m κ))).symm

/-- `ρ` only sees the coordinates `m κ ≥ N`. -/
theorem norm_localizationRho_le (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {ι : Type}
    [Fintype ι] [DecidableEq ι] {m : ι → ℕ} {N : ℕ} (hm : ∀ κ, N ≤ m κ)
    (x : BoundedMatrixSequence (fun n ↦ X n)) (c : ℝ) (hx : ∀ n, N ≤ n → ‖x n‖ ≤ c) :
    ‖localizationRho X m x‖ ≤ c :=
  norm_localization_blockDiagonal'_le (fun κ ↦ x (m κ)) ((norm_nonneg _).trans (hx N le_rfl))
    fun κ ↦ hx (m κ) (hm κ)

/-- The matrix with one nonzero row `z₀`, equal to `V p`. -/
def localizationRowFactor {Y Z : Type} [DecidableEq Z] (z₀ : Z) (V : Y → Z → ℂ) (p : Y) :
    Matrix Z Z ℂ :=
  Matrix.of fun r l ↦ if r = z₀ then V p l else 0

theorem localizationRowFactor_gram {Y Z : Type} [Fintype Z] [DecidableEq Z] (z₀ : Z)
    (V : Y → Z → ℂ) (p q : Y) (i j : Z) :
    (star (localizationRowFactor z₀ V p) * localizationRowFactor z₀ V q) i j =
      star (V p i) * V q j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single z₀]
  · simp [localizationRowFactor]
  · intro r _ hr
    simp [localizationRowFactor, hr]
  · intro h
    exact absurd (Finset.mem_univ z₀) h

/-- The rows `V ⟨κ, a⟩ = c κ · ξ_κ(·, a)`. -/
def localizationRowVector (X : ℕ → FiniteModel) {ι Z : Type} (m : ι → ℕ)
    (ξ : ∀ κ, Z × X (m κ) → ℂ) (c : ι → ℂ) : (Σ κ, X (m κ)) → Z → ℂ :=
  fun p l ↦ c p.1 * ξ p.1 (l, p.2)

theorem localization_rowChoi_apply {Y Z : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Z] [DecidableEq Z] [Nonempty Z] (z₀ : Z) (V : Y → Z → ℂ) (T : Matrix Y Y ℂ)
    (i j : Z) :
    BlackadarKirchberg.finiteMatrixRowChoiMap (localizationRowFactor z₀ V) T i j =
      ∑ p, star (V p i) * ∑ q, T p q * V q j := by
  simp only [BlackadarKirchberg.finiteMatrixRowChoiMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, localizationRowFactor_gram, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  ring

theorem localization_rowChoi_rho_apply (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) [Nonempty (Σ κ, X (m κ))]
    {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z] (z₀ : Z)
    (ξ : ∀ κ, Z × X (m κ) → ℂ) (c : ι → ℂ) (x : BoundedMatrixSequence (fun n ↦ X n))
    (i j : Z) :
    BlackadarKirchberg.finiteMatrixRowChoiMap
        (localizationRowFactor z₀ (localizationRowVector X m ξ c)) (localizationRho X m x) i j =
      ∑ κ, star (c κ) * c κ * ∑ a : X (m κ), ∑ b : X (m κ),
        star (ξ κ (i, a)) * x (m κ) a b * ξ κ (j, b) := by
  rw [localization_rowChoi_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have hmv : ∑ q, localizationRho X m x ⟨κ, a⟩ q * localizationRowVector X m ξ c q j =
      ∑ b : X (m κ), x (m κ) a b * (c κ * ξ κ (j, b)) :=
    localization_blockDiagonal'_mulVec (fun κ ↦ x (m κ))
      (fun q ↦ localizationRowVector X m ξ c q j) κ a
  rw [hmv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [localizationRowVector, star_mul']
  ring

theorem localization_rowChoi_rho_eq_smul (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) [Nonempty (Σ κ, X (m κ))]
    {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (z₀ : Z)
    (ξ : ∀ κ, Z × X (m κ) → ℂ) (w : ι → ℝ) (hw : ∀ κ, 0 ≤ w κ) {s : ℝ} (hs : 0 ≤ s)
    (x : BoundedMatrixSequence (fun n ↦ X n)) (hx : x ∈ T) (i j : Z) :
    BlackadarKirchberg.finiteMatrixRowChoiMap
        (localizationRowFactor z₀
          (localizationRowVector X m ξ fun κ ↦ ((Real.sqrt (s * w κ) : ℝ) : ℂ)))
        (localizationRho X m x) i j =
      (s : ℂ) * ∑ κ, (w κ : ℂ) * localizationVectorState X T (ξ κ) (i, j, ⟨x, hx⟩) := by
  rw [localization_rowChoi_rho_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  have hc : star ((Real.sqrt (s * w κ) : ℝ) : ℂ) * ((Real.sqrt (s * w κ) : ℝ) : ℂ) =
      ((s * w κ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (mul_nonneg hs (hw κ))]
  rw [hc, Complex.ofReal_mul, mul_assoc]
  rfl

theorem localization_final_estimate {K C ε s δ nx : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hs1 : 1 - s ≤ K * ε) (hnx0 : 0 ≤ nx) (hnxC : nx ≤ C)
    (hδ : ε * (1 + K * (1 + K * C)) = δ) :
    K * (ε + (1 - s) * nx) ≤ δ := by
  nlinarith [mul_nonneg (mul_nonneg hK hnx0) (sub_nonneg.2 hs1),
    mul_nonneg (mul_nonneg hK (mul_nonneg hK hε)) (sub_nonneg.2 hnxC), mul_nonneg hK hε]

/-- **Finite-coordinate localization of UCP maps out of the matrix corona.** -/
theorem coronaUCPFiniteCoordinateLocalization :
    CoronaUCPFiniteCoordinateLocalizationStatement := by
  intro X _ D _ _ _ Ext hExt hExt1 T δ hδ N
  classical
  obtain ⟨R⟩ := BlackadarKirchberg.exists_matrixUCPRetract_of_finiteDimensionalCStar D
  -- Step 1: the matrix-valued UCP map `Φ`.
  obtain ⟨Φ, hΦdef, hΦ⟩ :
      ∃ Φ : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] Matrix R.model R.model ℂ,
        (∀ x, Φ x = R.embedding (Ext (normMatrixCStarCoronaMk (fun n ↦ X n) x))) ∧
          IsCompletelyPositive Φ :=
    ⟨(R.embedding.toNonUnitalStarAlgHom : D →ₗ[ℂ] Matrix R.model R.model ℂ) ∘ₗ Ext ∘ₗ
        ((normMatrixCStarCoronaQuotient (fun n ↦ X n)).toNonUnitalStarAlgHom :
          BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)),
      fun _ ↦ rfl,
      (isCompletelyPositive_of_starAlgHom R.embedding.toNonUnitalStarAlgHom).comp
        (hExt.comp (isCompletelyPositive_of_starAlgHom
          (normMatrixCStarCoronaQuotient (fun n ↦ X n)).toNonUnitalStarAlgHom))⟩
  have hΦ1 : Φ 1 = 1 := by
    rw [hΦdef, map_one, hExt1, map_one]
  have htail : ∀ x : BoundedMatrixSequence (fun n ↦ X n),
      (∀ n, N ≤ n → x n = 0) → Φ x = 0 := by
    intro x hx
    have hmk : normMatrixCStarCoronaMk (fun n ↦ X n) x = 0 := by
      rw [normMatrixCStarCoronaMk_eq_zero_iff]
      show Filter.Tendsto (fun n ↦ ‖x n‖) Filter.cofinite (nhds 0)
      rw [Nat.cofinite_eq_atTop]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      simp only [hx n hn, norm_zero]
    rw [hΦdef, hmk, map_zero, map_zero]
  have hΦnorm : ∀ x, ‖Φ x‖ ≤ ‖x‖ := fun x ↦
    BlackadarKirchberg.norm_apply_le_of_ucp_finiteDimensionalTarget Φ hΦ hΦ1 x
  -- Step 2: the tolerances.
  obtain ⟨T', h1T', hTT'⟩ :
      ∃ T' : Finset (BoundedMatrixSequence (fun n ↦ X n)), 1 ∈ T' ∧ T ⊆ T' :=
    ⟨insert 1 T, Finset.mem_insert_self _ _, Finset.subset_insert _ _⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Fintype.card R.model : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ t ∈ T, ‖t‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact Finset.sum_nonneg fun t _ ↦ norm_nonneg t
  have hden : 0 < 1 + K * (1 + K * C) := by
    nlinarith [mul_nonneg hK0 (mul_nonneg hK0 hC0)]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / (1 + K * (1 + K * C)) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos hδ hden
  have hεδ : ε * (1 + K * (1 + K * C)) = δ := by
    rw [hεdef]
    exact div_mul_cancel₀ δ hden.ne'
  have hKε : 0 < 1 + K * ε := by
    nlinarith [mul_nonneg hK0 hε.le]
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (1 + K * ε)⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by
    rw [hsdef]
    exact inv_nonneg.mpr hKε.le
  have hs_eq : s * (1 + K * ε) = 1 := by
    rw [hsdef]
    exact inv_mul_cancel₀ hKε.ne'
  have hsle : s ≤ 1 := by
    nlinarith [mul_nonneg hs0 (mul_nonneg hK0 hε.le)]
  have hs1 : 1 - s ≤ K * ε := by
    nlinarith [mul_nonneg (sub_nonneg.2 hsle) (mul_nonneg hK0 hε.le)]
  -- Step 3: approximate the target point by a convex combination of vector states.
  obtain ⟨y, hyhull, hyclose⟩ :=
    BlackadarKirchberg.exists_convexHull_near_of_approximate_complex_support
      (localizationVectorStateSet X R.model T' N) (localizationTarget X T' Φ)
      (localization_support X T' Φ hΦ N htail) hε
  obtain ⟨ι, _, w, z, hw0, hw1, hzS, rfl⟩ := mem_convexHull_iff_exists_fintype.mp hyhull
  have hzS' : ∀ κ, ∃ n, N ≤ n ∧ ∃ ξ : R.model × X n → ℂ,
      z κ = localizationVectorState X T' ξ := hzS
  choose m hm ξ hξ using hzS'
  obtain ⟨κ₀⟩ : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp at hw1
    · exact hι
  haveI hYne : Nonempty (Σ κ, X (m κ)) := ⟨⟨κ₀, Classical.arbitrary _⟩⟩
  obtain ⟨z₀⟩ : Nonempty R.model := inferInstance
  have hyapp : ∀ p : R.model × R.model × T',
      (∑ κ, w κ • z κ) p = ∑ κ, (w κ : ℂ) * localizationVectorState X T' (ξ κ) p := by
    intro p
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    rw [Pi.smul_apply, Complex.real_smul, hξ κ]
  have hyp : ∀ p : R.model × R.model × T',
      ‖(∑ κ, w κ • z κ) p - localizationTarget X T' Φ p‖ < ε := fun p ↦
    lt_of_le_of_lt (norm_le_pi_norm (∑ κ, w κ • z κ - localizationTarget X T' Φ) p) hyclose
  -- Step 4: the compression `Ψ`.
  obtain ⟨Ψ, hΨ, hΨCP⟩ :
      ∃ Ψ : Matrix (Σ κ, X (m κ)) (Σ κ, X (m κ)) ℂ →ₗ[ℂ] Matrix R.model R.model ℂ,
        (∀ (x : BoundedMatrixSequence (fun n ↦ X n)) (hx : x ∈ T') (i j : R.model),
          Ψ (localizationRho X m x) i j =
            (s : ℂ) * ∑ κ, (w κ : ℂ) * localizationVectorState X T' (ξ κ) (i, j, ⟨x, hx⟩)) ∧
          IsCompletelyPositive Ψ :=
    ⟨BlackadarKirchberg.finiteMatrixRowChoiMap
        (localizationRowFactor z₀
          (localizationRowVector X m ξ fun κ ↦ ((Real.sqrt (s * w κ) : ℝ) : ℂ))),
      localization_rowChoi_rho_eq_smul X m T' z₀ ξ w hw0 hs0,
      BlackadarKirchberg.isCompletelyPositive_finiteMatrixRowChoiMap _⟩
  have hmain : ∀ (x : BoundedMatrixSequence (fun n ↦ X n)) (hx : x ∈ T') (i j : R.model),
      ‖Ψ (localizationRho X m x) i j - (s : ℂ) * Φ x i j‖ ≤ s * ε := by
    intro x hx i j
    have h := hyp (i, j, ⟨x, hx⟩)
    rw [hΨ x hx i j, ← hyapp (i, j, ⟨x, hx⟩), ← mul_sub, norm_mul, Complex.norm_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left h.le hs0
  have hρ1 : localizationRho X m 1 = 1 := by
    change Matrix.blockDiagonal'
      (fun κ ↦ (1 : BoundedMatrixSequence (fun n ↦ X n)) (m κ)) = 1
    exact Matrix.blockDiagonal'_one
  have hdiff1 : ‖Ψ 1 - (s : ℂ) • (1 : Matrix R.model R.model ℂ)‖ ≤ K * (s * ε) := by
    rw [hK]
    refine OperatorNormCertificate.opNorm_le_of_entry_bound _
      (mul_nonneg hs0 hε.le) fun i j ↦ ?_
    have h := hmain 1 h1T' i j
    rw [hρ1, hΦ1] at h
    exact h
  have hΨone : ‖Ψ 1‖ ≤ 1 := by
    calc ‖Ψ 1‖
        = ‖(Ψ 1 - (s : ℂ) • (1 : Matrix R.model R.model ℂ)) +
            (s : ℂ) • (1 : Matrix R.model R.model ℂ)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖Ψ 1 - (s : ℂ) • (1 : Matrix R.model R.model ℂ)‖ +
            ‖(s : ℂ) • (1 : Matrix R.model R.model ℂ)‖ := norm_add_le _ _
      _ ≤ K * (s * ε) + s := by
          rw [norm_smul, Complex.norm_of_nonneg hs0, CStarRing.norm_one, mul_one]
          linarith [hdiff1]
      _ = s * (1 + K * ε) := by ring
      _ = 1 := hs_eq
  -- Step 5: assemble `Y`, `ρ` and `θ = E ∘ Ψ`.
  refine ⟨⟨Σ κ, X (m κ), inferInstance, inferInstance⟩, hYne, localizationRho X m,
    R.retract ∘ₗ Ψ, ?_, ?_, ?_, ?_⟩
  · exact fun x c hx ↦ norm_localizationRho_le X hm x c hx
  · exact R.retract_completelyPositive.comp hΨCP
  · intro y
    calc ‖(R.retract ∘ₗ Ψ) y‖ = ‖R.retract (Ψ y)‖ := rfl
      _ ≤ ‖Ψ y‖ := R.retract_norm_le (Ψ y)
      _ ≤ ‖Ψ 1‖ * ‖y‖ :=
          BlackadarKirchberg.CStarExactness.IsCompletelyPositive.matrix_norm_apply_le_map_one
            Ψ hΨCP y
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hΨone (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  · intro x hxT
    have hx : x ∈ T' := hTT' hxT
    have hnx : ‖x‖ ≤ C := by
      rw [hC]
      exact Finset.single_le_sum (f := fun t ↦ ‖t‖) (fun t _ ↦ norm_nonneg t) hxT
    have hdiff : ‖Ψ (localizationRho X m x) - Φ x‖ ≤ K * (ε + (1 - s) * ‖x‖) := by
      rw [hK]
      refine OperatorNormCertificate.opNorm_le_of_entry_bound _
        (add_nonneg hε.le (mul_nonneg (sub_nonneg.2 hsle) (norm_nonneg x))) fun i j ↦ ?_
      have h := hmain x hx i j
      calc ‖(Ψ (localizationRho X m x) - Φ x) i j‖
          = ‖Ψ (localizationRho X m x) i j - Φ x i j‖ := rfl
        _ = ‖(Ψ (localizationRho X m x) i j - (s : ℂ) * Φ x i j) +
              ((1 - s : ℝ) : ℂ) * Φ x i j‖ := by
            congr 1
            push_cast
            ring
        _ ≤ ‖Ψ (localizationRho X m x) i j - (s : ℂ) * Φ x i j‖ +
              ‖((1 - s : ℝ) : ℂ) * Φ x i j‖ := norm_add_le _ _
        _ ≤ ε + (1 - s) * ‖x‖ := by
            refine add_le_add (h.trans (mul_le_of_le_one_left hε.le hsle)) ?_
            rw [norm_mul, Complex.norm_of_nonneg (sub_nonneg.2 hsle)]
            exact mul_le_mul_of_nonneg_left
              ((OperatorNormCertificate.norm_entry_le_opNorm _ i j).trans (hΦnorm x))
              (sub_nonneg.2 hsle)
    calc ‖(R.retract ∘ₗ Ψ) (localizationRho X m x) -
          Ext (normMatrixCStarCoronaMk (fun n ↦ X n) x)‖
        = ‖R.retract (Ψ (localizationRho X m x) - Φ x)‖ := by
          rw [LinearMap.comp_apply, map_sub, hΦdef x, R.retract_embedding]
      _ ≤ ‖Ψ (localizationRho X m x) - Φ x‖ := R.retract_norm_le _
      _ ≤ K * (ε + (1 - s) * ‖x‖) := hdiff
      _ ≤ δ := localization_final_estimate hK0 hε.le hs1 (norm_nonneg x) hnx hεδ

/-- **The printed sentence.** A separable C-star algebra is NF if and only if it is nuclear
and has an MF embedding. -/
theorem manuscriptSentence_blackadarKirchbergNFIff {A : Type u} [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A) :
    IsNFAlgebra A ↔ IsNuclearCStarAlgebra A ∧ HasMFEmbedding A :=
  blackadarKirchbergNFIff_of_coronaUCPFiniteCoordinateLocalization
    coronaUCPFiniteCoordinateLocalization hsep

end

end RelatedBK
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedBK

#audit_axioms localizationRho
#audit_axioms norm_localizationRho_le
#audit_axioms localizationRowFactor
#audit_axioms localizationRowFactor_gram
#audit_axioms localizationRowVector
#audit_axioms localization_rowChoi_apply
#audit_axioms localization_rowChoi_rho_apply
#audit_axioms localization_rowChoi_rho_eq_smul
#audit_axioms localization_final_estimate
#audit_axioms coronaUCPFiniteCoordinateLocalization
#audit_axioms manuscriptSentence_blackadarKirchbergNFIff
