import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.ProjectionRankFlip
import GroupApproximation.Sofic.KazhdanCapture
import GroupApproximation.Sofic.MarkedCompressionInclusionData

/-!
# The Kazhdan compressor corner

Steps 7–10 of the marked-compression kill argument.  Given an operator-norm
almost representation `B` of `E` and inclusion data `D`, the adjoint almost
representation of `Γ` carries a finite-stage Kazhdan spectral projection
`P`.  The compression relation `t · iota(Γ) · t⁻¹ ⊆ iota(Γ)` forces the
`t`-conjugate `Q` of `P` to almost contain `P` in operator norm, and the
equal-rank projection flip upgrades that one-sided containment to
`‖(1 - P) Q‖ → 0`.  This chain is the finite-dimensional substitute for
stable finiteness of a norm matrix corona.

The compression step never needs an endomorphism of `Γ`: for each averaged
generator `s` one chosen conjugate `δ` with `t (ι s) t⁻¹ = ι δ` suffices,
because the top-spectral displacement theorem applies to every element of
`Γ` at once.
-/

namespace GroupApproximation
namespace KazhdanCompressorCorner

open Matrix KazhdanCornerMatrices
open scoped ComplexOrder Matrix.Norms.L2Operator

/-! ## The vector capture inequality -/

/-- **Vector spectral capture.**  The mass of a vector below the spectral
threshold is controlled by its Laplacian energy.  This is the quadratic-form
shadow of the operator capture lemma
`one_sub_threshold_mul_norm_spectralBelow_mul_sq_le`, proved by the same
positive-semidefinite comparison matrix. -/
theorem capture_vec {Y : FiniteModel} (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) (t delta : ℝ) (ht : t ≤ 1) (hdelta : 0 ≤ delta)
    (hHnorm : ‖H‖ ≤ 1 + delta) (ξ : Y → ℂ) :
    (1 - t) * ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ ξ) i) ≤
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re +
        delta * ∑ i : Y, Complex.normSq (ξ i) := by
  classical
  let U : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let L : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let R : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then 0 else 1)
  let d : Y → ℝ := fun i ↦
    if t < hH.eigenvalues i then 1 - hH.eigenvalues i + delta
    else t - hH.eigenvalues i + delta
  let Bmat : Matrix Y Y ℂ :=
    1 - H + (delta : ℂ) • (1 : Matrix Y Y ℂ) -
      ((1 - t : ℝ) : ℂ) • spectralBelow H hH t
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hHdiag : H = U * L * Uᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = U * L * Uᴴ := by rfl
  have hRdiag : spectralBelow H hH t = U * R * Uᴴ := by
    unfold spectralBelow spectralAbove
    rw [← hUUstar]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : t < hH.eigenvalues i <;> simp [R, hi]
    · simp [R, hij]
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    by_cases hi : t < hH.eigenvalues i
    · simp only [d, hi, if_true]
      have heig := abs_hermitianEigenvalue_le_norm H hH i
      have hupper : hH.eigenvalues i ≤ 1 + delta :=
        (le_abs_self _).trans (heig.trans hHnorm)
      linarith
    · simp only [d, hi, if_false]
      exact add_nonneg (sub_nonneg.mpr (le_of_not_gt hi)) hdelta
  have hBdiag : Bmat = U * Matrix.diagonal (fun i ↦ (d i : ℂ)) * Uᴴ := by
    rw [show Bmat = 1 - H + (delta : ℂ) • 1 -
      ((1 - t : ℝ) : ℂ) • spectralBelow H hH t by rfl,
      hHdiag, hRdiag, ← hUUstar]
    have hdiag :
        (1 : Matrix Y Y ℂ) - L + (delta : ℂ) • 1 -
            ((1 - t : ℝ) : ℂ) • R =
          Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : t < hH.eigenvalues i <;>
          simp [L, R, d, hi] <;> push_cast <;> ring
      · simp [L, R, d, hij]
    rw [← hdiag]
    module
    noncomm_ring
  have hBpos : Bmat.PosSemidef := by
    rw [hBdiag]
    exact (diagonal_posSemidef_of_nonneg d hdnonneg).mul_mul_conjTranspose_same U
  -- expand the nonnegative quadratic form of `Bmat`
  have hform := hBpos.2 ξ
  have hre : 0 ≤ (star ξ ⬝ᵥ (Bmat *ᵥ ξ)).re := by
    have h := hform
    rw [Complex.le_def] at h
    simpa using h.1
  have hproj := spectralBelow_isOrthogonalProjection H hH t
  have hprojGram : (spectralBelow H hH t)ᴴ * spectralBelow H hH t =
      spectralBelow H hH t := by
    rw [hproj.1, hproj.2]
  have hmass : (star ξ ⬝ᵥ (spectralBelow H hH t *ᵥ ξ)).re =
      ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ ξ) i) := by
    have h := sum_normSq_mulVec_eq_re_gram_general (spectralBelow H hH t) ξ
    rw [hprojGram] at h
    exact h.symm
  have hexpand : (star ξ ⬝ᵥ (Bmat *ᵥ ξ)).re =
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re +
        delta * ∑ i : Y, Complex.normSq (ξ i) -
        (1 - t) * ∑ i : Y,
          Complex.normSq ((spectralBelow H hH t *ᵥ ξ) i) := by
    have hBvec : Bmat *ᵥ ξ =
        (ξ - H *ᵥ ξ) + (delta : ℂ) • ξ -
          ((1 - t : ℝ) : ℂ) • (spectralBelow H hH t *ᵥ ξ) := by
      show (1 - H + (delta : ℂ) • (1 : Matrix Y Y ℂ) -
          ((1 - t : ℝ) : ℂ) • spectralBelow H hH t) *ᵥ ξ = _
      rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
        Matrix.one_mulVec]
    rw [hBvec, dotProduct_sub, dotProduct_add, dotProduct_smul,
      dotProduct_smul, Complex.sub_re, Complex.add_re, smul_eq_mul,
      smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      re_dotProduct_self, hmass]
  linarith [hexpand ▸ hre]

/-! ## Unitary bookkeeping -/

/-- The conjugate transpose of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup {Y : Type*} [Fintype Y]
    [DecidableEq Y] {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) :
    uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact Unitary.star_mul_self_of_mem hu

/-! ## The finite-stage compressor data -/

universe u

variable {Γ : Type} [Group Γ] {E : Type u} [Group E]

/-- The adjoint almost representation of `Γ` induced along the inclusion. -/
abbrev gammaAdjoint (B : OpAlmostRepresentation E)
    (D : MarkedCompressionInclusionData Γ E) : OpAlmostRepresentation Γ :=
  B.adjoint.comap D.iota

variable (B : OpAlmostRepresentation E)
  (D : MarkedCompressionInclusionData Γ E) (S : Finset Γ) (θ : ℝ)

/-- The finite-stage Kazhdan spectral projection of the adjoint corner. -/
noncomputable def cornerProjection (n : ℕ) :
    Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
  spectralAbove (hermitianAverage (gammaAdjoint B D) S n)
    (hermitianAverage_conjTranspose (gammaAdjoint B D) S n) θ

/-- The `t`-conjugate of the corner projection. -/
noncomputable def movedProjection (n : ℕ) :
    Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
  (B.adjoint.map n D.t : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
    cornerProjection B D S θ n *
    (B.adjoint.map n D.t : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ

theorem cornerProjection_isOrthogonalProjection (n : ℕ) :
    IsOrthogonalProjectionMatrix (cornerProjection B D S θ n) :=
  spectralAbove_isOrthogonalProjection _ _ _

theorem norm_cornerProjection_le_one (n : ℕ) :
    ‖cornerProjection B D S θ n‖ ≤ 1 :=
  norm_spectralAbove_le_one _ _ _

theorem movedProjection_isOrthogonalProjection (n : ℕ) :
    IsOrthogonalProjectionMatrix (movedProjection B D S θ n) :=
  unitary_conjugate_isOrthogonalProjection (B.adjoint.map n D.t).2
    (cornerProjection_isOrthogonalProjection B D S θ n)

theorem movedProjection_rank (n : ℕ) :
    (movedProjection B D S θ n).rank = (cornerProjection B D S θ n).rank :=
  rank_unitary_conj (B.adjoint.map n D.t).2 _

/-! ## Step 7: displacement of the corner by every element of `Γ` -/

variable {S}

/-- Every fixed element of `Γ` almost fixes the range of the corner
projection, uniformly in operator norm. -/
theorem displacement_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (γ : Γ) :
    OpNormVanishing (gammaAdjoint B D) (fun n ↦
      ((gammaAdjoint B D).map n γ -
          (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)) *
        cornerProjection B D S θ n) := by
  have h := topSpectralDisplacement_vanishing_of_generates hQ S
    (Finset.Subset.refl S) hone hκ1 hsymm hgen (gammaAdjoint B D) hθ4 γ
  exact h.congr fun n ↦ by
    rw [topSpectralDisplacement]
    rfl

/-! ## Step 9: the conjugation chain -/

/-- The adjoint microstate of a compressed generator almost intertwines the
`t`-conjugation: `β(ι s) · β(t)ᴴ ≈ β(t)ᴴ · β(ι δ)` whenever
`t (ι s) t⁻¹ = ι δ`. -/
theorem conj_defect_vanishing {s δ : Γ}
    (hrel : D.t * D.iota s * D.t⁻¹ = D.iota δ) :
    OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (D.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        (B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ -
      (B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        B.adjoint.map n (D.iota δ)) := by
  have hgroup : D.iota s * D.t⁻¹ = D.t⁻¹ * D.iota δ := by
    rw [← hrel]
    group
  have hnormlemma : ∀ n, ∀ x :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ,
      x ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ → ‖x‖ ≤ 1 := by
    intro n x hx
    letI : Nonempty (B.adjoint.model n) :=
      Fintype.card_pos_iff.mp (B.adjoint.modelNonempty n)
    exact le_of_eq (CStarRing.norm_of_mem_unitary hx)
  -- four vanishing pieces
  have h1 : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (D.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        ((B.adjoint.map n D.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ -
          B.adjoint.map n D.t⁻¹)) := by
    have hinv := (map_inv_vanishing B.adjoint D.t).neg
    have := hinv.mul_left_of_norm_le_one
      (fun n ↦ (B.adjoint.map n (D.iota s) :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ))
      (fun n ↦ hnormlemma n _ (B.adjoint.map n (D.iota s)).2)
    exact this.congr fun n ↦ by rw [neg_sub, Matrix.mul_sub, Matrix.mul_sub]
  have h2 : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (D.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        B.adjoint.map n D.t⁻¹ -
      B.adjoint.map n (D.iota s * D.t⁻¹)) :=
    (multiplicativeDefect_vanishing B.adjoint (D.iota s) D.t⁻¹).neg.congr
      fun n ↦ by rw [neg_sub]
  have h3 : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (D.t⁻¹ * D.iota δ) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      B.adjoint.map n D.t⁻¹ * B.adjoint.map n (D.iota δ)) :=
    multiplicativeDefect_vanishing B.adjoint D.t⁻¹ (D.iota δ)
  have h4 : OpNormVanishing B.adjoint (fun n ↦
      ((B.adjoint.map n D.t⁻¹ :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        (B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        B.adjoint.map n (D.iota δ)) :=
    (map_inv_vanishing B.adjoint D.t).mul_right_of_norm_le_one
      (fun n ↦ (B.adjoint.map n (D.iota δ) :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ))
      (fun n ↦ hnormlemma n _ (B.adjoint.map n (D.iota δ)).2)
  refine (((h1.add h2).add h3).add h4).congr fun n ↦ ?_
  rw [hgroup]
  noncomm_ring

/-! ## Step 9: one-sided leakage of the rotated corner -/

/-- The rotated corner `β(t)ᴴ · P` is almost fixed by every averaged
generator microstate. -/
theorem one_sub_map_mul_rotated_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (s : Γ) :
    OpNormVanishing B.adjoint (fun n ↦
      ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          B.adjoint.map n (D.iota s)) *
        ((B.adjoint.map n D.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B D S θ n)) := by
  obtain ⟨δ, hrel⟩ := D.compresses s
  have hnormT : ∀ n, ‖(B.adjoint.map n D.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro n
    letI : Nonempty (B.adjoint.model n) :=
      Fintype.card_pos_iff.mp (B.adjoint.modelNonempty n)
    exact le_of_eq (CStarRing.norm_of_mem_unitary
      (conjTranspose_mem_unitaryGroup (B.adjoint.map n D.t).2))
  -- first piece: the displacement at δ, rotated by the unitary `β(t)ᴴ`
  have hfirst : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        (((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            B.adjoint.map n (D.iota δ)) *
          cornerProjection B D S θ n)) := by
    have hdisp := displacement_vanishing B D θ hQ hone hκ1 hsymm hgen hθ4 δ
    have hneg := hdisp.neg
    have := hneg.mul_left_of_norm_le_one
      (fun n ↦ (B.adjoint.map n D.t :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) hnormT
    exact this.congr fun n ↦ by
      rw [neg_mul, ← Matrix.neg_mul, neg_sub]
      rfl
  -- second piece: the conjugation chain against the projection
  have hsecond : OpNormVanishing B.adjoint (fun n ↦
      ((B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        B.adjoint.map n (D.iota δ) -
        (B.adjoint.map n (D.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        (B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        cornerProjection B D S θ n) :=
    ((conj_defect_vanishing B D hrel).neg.congr (fun n ↦ by
      rw [neg_sub])).mul_right_of_norm_le_one
      (fun n ↦ cornerProjection B D S θ n)
      (fun n ↦ norm_cornerProjection_le_one B D S θ n)
  refine (hfirst.add hsecond).congr fun n ↦ ?_
  noncomm_ring

/-- Conjugate-transposed version: the rotated corner is also almost fixed by
the adjoints of the averaged generator microstates. -/
theorem one_sub_mapStar_mul_rotated_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (s : Γ) :
    OpNormVanishing B.adjoint (fun n ↦
      ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          (B.adjoint.map n (D.iota s) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        ((B.adjoint.map n D.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B D S θ n)) := by
  have hrotnorm : ∀ n, ‖(B.adjoint.map n D.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
      cornerProjection B D S θ n‖ ≤ 1 := by
    intro n
    calc
      ‖(B.adjoint.map n D.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        cornerProjection B D S θ n‖ =
          ‖cornerProjection B D S θ n‖ :=
        CStarRing.norm_mem_unitary_mul _
          (conjTranspose_mem_unitaryGroup (B.adjoint.map n D.t).2)
      _ ≤ 1 := norm_cornerProjection_le_one B D S θ n
  -- replace the conjugate transpose by the microstate of the inverse
  have hinvdiff : OpNormVanishing B.adjoint (fun n ↦
      ((B.adjoint.map n (D.iota s⁻¹) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        (B.adjoint.map n (D.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        ((B.adjoint.map n D.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B D S θ n)) := by
    have h := map_inv_vanishing B.adjoint (D.iota s)
    have h' : OpNormVanishing B.adjoint (fun n ↦
        (B.adjoint.map n (D.iota s⁻¹) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          (B.adjoint.map n (D.iota s) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) := by
      have hcongr : ∀ n,
          (B.adjoint.map n (D.iota s)⁻¹ :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (B.adjoint.map n (D.iota s) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ =
          (B.adjoint.map n (D.iota s⁻¹) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (B.adjoint.map n (D.iota s) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ := by
        intro n
        rw [map_inv]
      exact h.congr hcongr
    exact h'.mul_right_of_norm_le_one _ hrotnorm
  have hmain := one_sub_map_mul_rotated_vanishing B D θ hQ hone hκ1 hsymm
    hgen hθ4 s⁻¹
  refine (hmain.add hinvdiff).congr fun n ↦ ?_
  noncomm_ring

/-! ## Step 9: displacement of the rotated corner by the Hermitian average -/

/-- The Laplacian displacement of the rotated corner vanishes: the Hermitian
average almost fixes `β(t)ᴴ · P`. -/
theorem rotated_laplacian_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) :
    OpNormVanishing B.adjoint (fun n ↦
      ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          hermitianAverage (gammaAdjoint B D) S n) *
        ((B.adjoint.map n D.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B D S θ n)) := by
  classical
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hcardC : ((S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, hone⟩
  -- the sum of the per-generator pieces vanishes
  have hsum : OpNormVanishing B.adjoint (fun n ↦
      ∑ s ∈ S,
        (((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            B.adjoint.map n (D.iota s)) *
          ((B.adjoint.map n D.t :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
            cornerProjection B D S θ n) +
        ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (B.adjoint.map n (D.iota s) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
          ((B.adjoint.map n D.t :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
            cornerProjection B D S θ n))) := by
    refine OpNormVanishing.finset_sum S _ fun s _ ↦ ?_
    exact (one_sub_map_mul_rotated_vanishing B D θ hQ hone hκ1 hsymm hgen
      hθ4 s).add
      (one_sub_mapStar_mul_rotated_vanishing B D θ hQ hone hκ1 hsymm hgen
        hθ4 s)
  have hscaled := (hsum.smul ((S.card : ℂ)⁻¹)).smul ((2 : ℂ)⁻¹)
  refine hscaled.congr fun n ↦ ?_
  -- the exact average identity
  set X : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    (B.adjoint.map n D.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
      cornerProjection B D S θ n with hX
  have honeM : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) =
      (S.card : ℂ)⁻¹ • ∑ _s ∈ S,
        (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcardC, one_smul]
  have hM : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      matrixAverage (gammaAdjoint B D) S n =
      (S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          B.adjoint.map n (D.iota s)) := by
    rw [matrixAverage, Finset.sum_sub_distrib, smul_sub, ← honeM]
    rfl
  have hMstar : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      (matrixAverage (gammaAdjoint B D) S n)ᴴ =
      (S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          (B.adjoint.map n (D.iota s) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) := by
    have h := congrArg Matrix.conjTranspose hM
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_sum] at h
    have hstarcard : (star ((S.card : ℂ)⁻¹)) = ((S.card : ℂ))⁻¹ := by
      rw [star_inv₀]
      norm_cast
    rw [hstarcard] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have hHsplit : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      hermitianAverage (gammaAdjoint B D) S n =
      (2 : ℂ)⁻¹ •
        (((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            matrixAverage (gammaAdjoint B D) S n) +
          ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (matrixAverage (gammaAdjoint B D) S n)ᴴ)) := by
    rw [hermitianAverage]
    module
  rw [hHsplit, hM, hMstar, ← smul_add, ← Finset.sum_add_distrib,
    Matrix.smul_mul, Matrix.smul_mul, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Matrix.add_mul]

/-! ## Step 9 conclusion: one-sided containment `‖(1 - Q) P‖ → 0` -/

/-- The moved projection almost contains the corner projection. -/
theorem one_sub_moved_mul_corner_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (hθ1 : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          movedProjection B D S θ n) * cornerProjection B D S θ n‖ ≤ ε := by
  intro ε hε
  have hθpos : 0 < 1 - θ := by linarith
  obtain ⟨N, hN⟩ := rotated_laplacian_vanishing B D θ hQ hone hκ1 hsymm hgen
    hθ4 ((1 - θ) * ε ^ 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  set T : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    (B.adjoint.map n D.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) with hT
  set P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    cornerProjection B D S θ n with hP
  have hTmem : T ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
    (B.adjoint.map n D.t).2
  have hTstar : T * Tᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hTmem
    rwa [Matrix.star_eq_conjTranspose] at h
  -- rewrite `(1 - Q) P` as a unitary times the spectral-below compression
  have hfactor : ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      movedProjection B D S θ n) * P =
      T * (spectralBelow (hermitianAverage (gammaAdjoint B D) S n)
        (hermitianAverage_conjTranspose (gammaAdjoint B D) S n) θ *
        (Tᴴ * P)) := by
    unfold spectralBelow
    rw [movedProjection]
    have : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        T * P * Tᴴ = T * (1 - P) * Tᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hTstar]
    rw [this, hP]
    unfold cornerProjection
    noncomm_ring
  rw [hfactor, CStarRing.norm_mem_unitary_mul _ hTmem]
  -- apply the operator capture lemma with `delta = 0`
  have hC : ‖Tᴴ * P‖ ≤ 1 := by
    calc
      ‖Tᴴ * P‖ = ‖P‖ :=
        CStarRing.norm_mem_unitary_mul _
          (conjTranspose_mem_unitaryGroup hTmem)
      _ ≤ 1 := norm_cornerProjection_le_one B D S θ n
  have hcapture := one_sub_threshold_mul_norm_spectralBelow_mul_sq_le
    (hermitianAverage (gammaAdjoint B D) S n)
    (hermitianAverage_conjTranspose (gammaAdjoint B D) S n)
    (Tᴴ * P) θ 0 hθ1.le le_rfl
    (by simpa using norm_hermitianAverage_le_one (gammaAdjoint B D) S n)
    hC
  have hdisp : ‖Tᴴ * P - hermitianAverage (gammaAdjoint B D) S n *
      (Tᴴ * P)‖ ≤ (1 - θ) * ε ^ 2 := by
    have h := hN n hn
    have hrw : ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        hermitianAverage (gammaAdjoint B D) S n) * (Tᴴ * P) =
        Tᴴ * P - hermitianAverage (gammaAdjoint B D) S n * (Tᴴ * P) := by
      rw [Matrix.sub_mul, Matrix.one_mul]
    rw [← hrw]
    exact h
  have hsq : (1 - θ) * ‖spectralBelow
      (hermitianAverage (gammaAdjoint B D) S n)
      (hermitianAverage_conjTranspose (gammaAdjoint B D) S n) θ *
      (Tᴴ * P)‖ ^ 2 ≤ (1 - θ) * ε ^ 2 := by
    calc
      (1 - θ) * ‖spectralBelow (hermitianAverage (gammaAdjoint B D) S n)
          (hermitianAverage_conjTranspose (gammaAdjoint B D) S n) θ *
          (Tᴴ * P)‖ ^ 2 ≤
          ‖Tᴴ * P - hermitianAverage (gammaAdjoint B D) S n *
            (Tᴴ * P)‖ + 0 := hcapture
      _ ≤ (1 - θ) * ε ^ 2 := by
        rw [add_zero]
        exact hdisp
  have hnormsq : ‖spectralBelow (hermitianAverage (gammaAdjoint B D) S n)
      (hermitianAverage_conjTranspose (gammaAdjoint B D) S n) θ *
      (Tᴴ * P)‖ ^ 2 ≤ ε ^ 2 := by
    have := (mul_le_mul_left hθpos).mp hsq
    exact this
  have hnn : 0 ≤ ‖spectralBelow (hermitianAverage (gammaAdjoint B D) S n)
      (hermitianAverage_conjTranspose (gammaAdjoint B D) S n) θ *
      (Tᴴ * P)‖ := norm_nonneg _
  nlinarith [hnormsq, hnn, hε.le]

/-! ## Step 10: the equal-rank flip -/

/-- **Two-sided compressor control.**  The corner projection almost contains
the moved projection: the finite-stage stable-finiteness step. -/
theorem one_sub_corner_mul_moved_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (hθ1 : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          cornerProjection B D S θ n) * movedProjection B D S θ n‖ ≤ ε := by
  intro ε hε
  set ε' : ℝ := min (1 / 2) (ε / 2) with hε'
  have hε'pos : 0 < ε' := lt_min (by norm_num) (by linarith)
  have hε'half : ε' ≤ 1 / 2 := min_le_left _ _
  have hε'lt1 : ε' < 1 := lt_of_le_of_lt hε'half (by norm_num)
  obtain ⟨N, hN⟩ := one_sub_moved_mul_corner_vanishing B D θ hQ hone hκ1
    hsymm hgen hθ4 hθ1 ε' hε'pos
  refine ⟨N, fun n hn ↦ ?_⟩
  have hflip := norm_one_sub_mul_flip
    (cornerProjection_isOrthogonalProjection B D S θ n)
    (movedProjection_isOrthogonalProjection B D S θ n)
    (movedProjection_rank B D S θ n).symm hε'pos.le hε'lt1 (hN n hn)
  -- the constant: `ε' / √(1 - ε'²) ≤ 2 ε' ≤ ε`
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt (1 - ε' ^ 2) := by
    have h34 : (1 : ℝ) / 4 ≤ 1 - ε' ^ 2 := by nlinarith [hε'half, hε'pos.le]
    calc
      (1 : ℝ) / 2 = Real.sqrt (1 / 4) := by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (1 - ε' ^ 2) := Real.sqrt_le_sqrt h34
  have hsqrtpos : 0 < Real.sqrt (1 - ε' ^ 2) := by linarith
  have hdivbound : ε' / Real.sqrt (1 - ε' ^ 2) ≤ 2 * ε' := by
    rw [div_le_iff₀ hsqrtpos]
    nlinarith [hsqrt, hε'pos.le]
  calc
    ‖((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        cornerProjection B D S θ n) * movedProjection B D S θ n‖ ≤
        ε' / Real.sqrt (1 - ε' ^ 2) := hflip
    _ ≤ 2 * ε' := hdivbound
    _ ≤ ε := by
      have := min_le_right (1 / 2 : ℝ) (ε / 2)
      calc
        2 * ε' ≤ 2 * (ε / 2) := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ = ε := by ring

end KazhdanCompressorCorner
end GroupApproximation
