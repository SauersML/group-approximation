import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.SpectralCapture
import GroupApproximation.Sofic.KazhdanCompressionCore

/-!
# The Kazhdan compressor corner

Steps 7–10 of the marked-compression kill argument.  Given an operator-norm
almost representation `B` of `E` and inclusion data `C`, the adjoint almost
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

The operator-norm-to-Hilbert--Schmidt conjugation maneuver has an older
ancestor in Dadarlat, Lemma 3.18 and Proposition 3.19 (Ozawa--Thom),
*Obstructions to matricial stability of discrete groups and almost flat
K-theory*.  The one-sided-compressor/fixed-space architecture is also the
finite-stage operator-norm analogue of OpenAI, Proposition 2.3, and of the
compression-semigroup and sofic-Mautner framework of Kun--Thom
(arXiv:2608.06222).  For robust spectral separation of operator-norm almost
representations of property-(T) groups, the closest finite-stage precedent is
the proof of Uri Bader recorded as Dogon--Vigdorovich, arXiv:2506.20843,
Theorem 7.10; it uses Ozawa's sum-of-squares characterization and generalizes
Manuilov--You.  The equal-rank reversal below is this development's
finite-dimensional replacement for stable finiteness; no external code is
copied.
-/

namespace GroupApproximation
namespace KazhdanCompressorCorner

open Matrix KazhdanCornerMatrices
open scoped ComplexOrder Matrix.Norms.L2Operator

/-! ## The vector capture inequality -/

/-- **Vector spectral capture.**  The mass of a vector below the spectral
threshold is controlled by its Laplacian energy.  This is the quadratic-form
shadow of the operator capture lemma `norm_spectralBelow_mul_sq_le`, proved
by the same positive-semidefinite comparison matrix. -/
theorem capture_vec {Y : FiniteModel} (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) (t delta : ℝ) (_ht : t ≤ 1) (hdelta : 0 ≤ delta)
    (hHnorm : ‖H‖ ≤ 1 + delta) (ξ : Y → ℂ) :
    (1 - t) * ∑ i : Y, Complex.normSq ((spectralBelow H hH t *ᵥ ξ) i) ≤
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re +
        delta * ∑ i : Y, Complex.normSq (ξ i) := by
  have h := spectralBelow_quadratic_bound hH hdelta hHnorm (t := t) ξ
  have hvec : (1 - H) *ᵥ ξ = ξ - H *ᵥ ξ := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rwa [hvec] at h

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
    (C : KazhdanCompressionCore Γ E) : OpAlmostRepresentation Γ :=
  B.adjoint.comap C.iota

variable (B : OpAlmostRepresentation E)
  (C : KazhdanCompressionCore Γ E) (S : Finset Γ) (θ : ℝ)

/-- The finite-stage Kazhdan spectral projection of the adjoint corner. -/
noncomputable def cornerProjection (n : ℕ) :
    Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
  spectralAbove (hermitianAverage (gammaAdjoint B C) S n)
    (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ

/-- The `t`-conjugate of the corner projection. -/
noncomputable def movedProjection (n : ℕ) :
    Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
  (B.adjoint.map n C.t : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
    cornerProjection B C S θ n *
    (B.adjoint.map n C.t : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ

theorem cornerProjection_isOrthogonalProjection (n : ℕ) :
    IsOrthogonalProjectionMatrix (cornerProjection B C S θ n) :=
  spectralAbove_isOrthogonalProjection _ _ _

theorem norm_cornerProjection_le_one (n : ℕ) :
    ‖cornerProjection B C S θ n‖ ≤ 1 :=
  norm_spectralAbove_le_one _ _ _

theorem movedProjection_isOrthogonalProjection (n : ℕ) :
    IsOrthogonalProjectionMatrix (movedProjection B C S θ n) :=
  unitary_conjugate_isOrthogonalProjection (B.adjoint.map n C.t).2
    (cornerProjection_isOrthogonalProjection B C S θ n)

theorem movedProjection_rank (n : ℕ) :
    (movedProjection B C S θ n).rank = (cornerProjection B C S θ n).rank :=
  rank_unitary_conj (B.adjoint.map n C.t).2 _

/-! ## Step 7: displacement of the corner by every element of `Γ` -/

variable {S}

/-- Every fixed element of `Γ` almost fixes the range of the corner
projection, uniformly in operator norm. -/
theorem displacement_vanishing {κ : ℝ}
    (hQ : IsKazhdanPair.{0, 0} Γ S κ) (hone : 1 ∈ S) (hκ1 : κ ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hθ4 : 1 - κ ^ 2 / (4 * S.card) < θ) (γ : Γ) :
    OpNormVanishing (gammaAdjoint B C) (fun n ↦
      ((gammaAdjoint B C).map n γ -
          (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)) *
        cornerProjection B C S θ n) := by
  have h := topSpectralDisplacement_vanishing_of_generates hQ S
    (Finset.Subset.refl S) hone hκ1 hsymm hgen (gammaAdjoint B C) hθ4 γ
  exact h.congr fun n ↦ by
    rw [topSpectralDisplacement]
    rfl

/-! ## Step 9: the conjugation chain -/

/-- The adjoint microstate of a compressed generator almost intertwines the
`t`-conjugation: `β(ι s) · β(t)ᴴ ≈ β(t)ᴴ · β(ι δ)` whenever
`t (ι s) t⁻¹ = ι δ`. -/
theorem conj_defect_vanishing {s δ : Γ}
    (hrel : C.t * C.iota s * C.t⁻¹ = C.iota δ) :
    OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (C.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        (B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ -
      (B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        B.adjoint.map n (C.iota δ)) := by
  have hgroup : C.iota s * C.t⁻¹ = C.t⁻¹ * C.iota δ := by
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
      (B.adjoint.map n (C.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        ((B.adjoint.map n C.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ -
          B.adjoint.map n C.t⁻¹)) := by
    have hinv := (map_inv_vanishing B.adjoint C.t).neg
    have := hinv.mul_left_of_norm_le_one
      (fun n ↦ (B.adjoint.map n (C.iota s) :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ))
      (fun n ↦ hnormlemma n _ (B.adjoint.map n (C.iota s)).2)
    exact this.congr fun n ↦ by noncomm_ring
  have h2 : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (C.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        B.adjoint.map n C.t⁻¹ -
      B.adjoint.map n (C.iota s * C.t⁻¹)) :=
    (multiplicativeDefect_vanishing B.adjoint (C.iota s) C.t⁻¹).neg.congr
      fun n ↦ by rw [neg_sub]
  have h3 : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n (C.t⁻¹ * C.iota δ) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      B.adjoint.map n C.t⁻¹ * B.adjoint.map n (C.iota δ)) :=
    multiplicativeDefect_vanishing B.adjoint C.t⁻¹ (C.iota δ)
  have h4 : OpNormVanishing B.adjoint (fun n ↦
      ((B.adjoint.map n C.t⁻¹ :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        (B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        B.adjoint.map n (C.iota δ)) :=
    (map_inv_vanishing B.adjoint C.t).mul_right_of_norm_le_one
      (fun n ↦ (B.adjoint.map n (C.iota δ) :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ))
      (fun n ↦ hnormlemma n _ (B.adjoint.map n (C.iota δ)).2)
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
          B.adjoint.map n (C.iota s)) *
        ((B.adjoint.map n C.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B C S θ n)) := by
  obtain ⟨δ, hrel⟩ := C.compresses s
  have hnormT : ∀ n, ‖(B.adjoint.map n C.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro n
    letI : Nonempty (B.adjoint.model n) :=
      Fintype.card_pos_iff.mp (B.adjoint.modelNonempty n)
    exact le_of_eq (CStarRing.norm_of_mem_unitary
      (conjTranspose_mem_unitaryGroup (B.adjoint.map n C.t).2))
  -- first piece: the displacement at δ, rotated by the unitary `β(t)ᴴ`
  have hfirst : OpNormVanishing B.adjoint (fun n ↦
      (B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        (((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            B.adjoint.map n (C.iota δ)) *
          cornerProjection B C S θ n)) := by
    have hdisp := displacement_vanishing B C θ hQ hone hκ1 hsymm hgen hθ4 δ
    have hneg := hdisp.neg
    have := hneg.mul_left_of_norm_le_one
      (fun n ↦ (B.adjoint.map n C.t :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) hnormT
    exact this.congr fun n ↦ by
      simp only [gammaAdjoint]
      noncomm_ring
  -- second piece: the conjugation chain against the projection
  have hsecond : OpNormVanishing B.adjoint (fun n ↦
      ((B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        B.adjoint.map n (C.iota δ) -
        (B.adjoint.map n (C.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        (B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        cornerProjection B C S θ n) :=
    ((conj_defect_vanishing B C hrel).neg.congr (fun n ↦ by
      rw [neg_sub])).mul_right_of_norm_le_one
      (fun n ↦ cornerProjection B C S θ n)
      (fun n ↦ norm_cornerProjection_le_one B C S θ n)
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
          (B.adjoint.map n (C.iota s) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        ((B.adjoint.map n C.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B C S θ n)) := by
  have hrotnorm : ∀ n, ‖(B.adjoint.map n C.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
      cornerProjection B C S θ n‖ ≤ 1 := by
    intro n
    calc
      ‖(B.adjoint.map n C.t :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
        cornerProjection B C S θ n‖ =
          ‖cornerProjection B C S θ n‖ :=
        CStarRing.norm_mem_unitary_mul _
          (conjTranspose_mem_unitaryGroup (B.adjoint.map n C.t).2)
      _ ≤ 1 := norm_cornerProjection_le_one B C S θ n
  -- replace the conjugate transpose by the microstate of the inverse
  have hinvdiff : OpNormVanishing B.adjoint (fun n ↦
      ((B.adjoint.map n (C.iota s⁻¹) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        (B.adjoint.map n (C.iota s) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
        ((B.adjoint.map n C.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B C S θ n)) := by
    have h := map_inv_vanishing B.adjoint (C.iota s)
    have h' : OpNormVanishing B.adjoint (fun n ↦
        (B.adjoint.map n (C.iota s⁻¹) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          (B.adjoint.map n (C.iota s) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) := by
      have hcongr : ∀ n,
          (B.adjoint.map n (C.iota s)⁻¹ :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (B.adjoint.map n (C.iota s) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ =
          (B.adjoint.map n (C.iota s⁻¹) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (B.adjoint.map n (C.iota s) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ := by
        intro n
        rw [map_inv]
      exact h.congr hcongr
    exact h'.mul_right_of_norm_le_one _ hrotnorm
  have hmain := one_sub_map_mul_rotated_vanishing B C θ hQ hone hκ1 hsymm
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
          hermitianAverage (gammaAdjoint B C) S n) *
        ((B.adjoint.map n C.t :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
          cornerProjection B C S θ n)) := by
  classical
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hcardC : ((S.card : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, hone⟩
  -- the sum of the per-generator pieces vanishes
  have hsum : OpNormVanishing B.adjoint (fun n ↦
      ∑ s ∈ S,
        (((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            B.adjoint.map n (C.iota s)) *
          ((B.adjoint.map n C.t :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
            cornerProjection B C S θ n) +
        ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (B.adjoint.map n (C.iota s) :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) *
          ((B.adjoint.map n C.t :
              Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
            cornerProjection B C S θ n))) := by
    refine OpNormVanishing.finset_sum S _ fun s _ ↦ ?_
    exact (one_sub_map_mul_rotated_vanishing B C θ hQ hone hκ1 hsymm hgen
      hθ4 s).add
      (one_sub_mapStar_mul_rotated_vanishing B C θ hQ hone hκ1 hsymm hgen
        hθ4 s)
  have hscaled := (hsum.smul ((S.card : ℂ)⁻¹)).smul ((2 : ℂ)⁻¹)
  refine hscaled.congr fun n ↦ ?_
  -- the exact average identity
  set X : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    (B.adjoint.map n C.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ *
      cornerProjection B C S θ n with hX
  have honeM : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) =
      (S.card : ℂ)⁻¹ • ∑ _s ∈ S,
        (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcardC, one_smul]
  have hM : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      matrixAverage (gammaAdjoint B C) S n =
      (S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          B.adjoint.map n (C.iota s)) := by
    unfold matrixAverage
    rw [Finset.sum_sub_distrib, smul_sub, ← honeM]
  have hMstar : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      (matrixAverage (gammaAdjoint B C) S n)ᴴ =
      (S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
          (B.adjoint.map n (C.iota s) :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) := by
    have h := congrArg Matrix.conjTranspose hM
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_sum] at h
    have hstarcard : (star ((S.card : ℂ)⁻¹)) = ((S.card : ℂ))⁻¹ := by
      rw [star_inv₀, star_natCast]
    rw [hstarcard] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have hHsplit : (1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      hermitianAverage (gammaAdjoint B C) S n =
      (2 : ℂ)⁻¹ •
        (((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            matrixAverage (gammaAdjoint B C) S n) +
          ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
            (matrixAverage (gammaAdjoint B C) S n)ᴴ)) := by
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
          movedProjection B C S θ n) * cornerProjection B C S θ n‖ ≤ ε := by
  intro ε hε
  have hθpos : 0 < 1 - θ := sub_pos.mpr hθ1
  obtain ⟨N, hN⟩ := rotated_laplacian_vanishing B C θ hQ hone hκ1 hsymm hgen
    hθ4 ((1 - θ) * ε ^ 2) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  set T : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    (B.adjoint.map n C.t :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) with hT
  set P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    cornerProjection B C S θ n with hP
  have hTmem : T ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
    (B.adjoint.map n C.t).2
  have hTstar : T * Tᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hTmem
    rwa [Matrix.star_eq_conjTranspose] at h
  -- rewrite `(1 - Q) P` as a unitary times the spectral-below compression
  have hfactor : ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
      movedProjection B C S θ n) * P =
      T * (spectralBelow (hermitianAverage (gammaAdjoint B C) S n)
        (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ *
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
      _ ≤ 1 := norm_cornerProjection_le_one B C S θ n
  have hcapture := norm_spectralBelow_mul_sq_le
    (hermitianAverage_conjTranspose (gammaAdjoint B C) S n)
    (show 0 ≤ (0 : ℝ) by norm_num)
    (by simpa using norm_hermitianAverage_le_one (gammaAdjoint B C) S n)
    hθ1 hC
  have hdisp : ‖Tᴴ * P - hermitianAverage (gammaAdjoint B C) S n *
      (Tᴴ * P)‖ ≤ (1 - θ) * ε ^ 2 := by
    have h := hN n hn
    have hrw : ((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        hermitianAverage (gammaAdjoint B C) S n) * (Tᴴ * P) =
        Tᴴ * P - hermitianAverage (gammaAdjoint B C) S n * (Tᴴ * P) := by
      rw [Matrix.sub_mul, Matrix.one_mul]
    rw [← hrw]
    exact h
  have hsq : (1 - θ) * ‖spectralBelow
      (hermitianAverage (gammaAdjoint B C) S n)
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ *
      (Tᴴ * P)‖ ^ 2 ≤ (1 - θ) * ε ^ 2 := by
    calc
      (1 - θ) * ‖spectralBelow (hermitianAverage (gammaAdjoint B C) S n)
          (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ *
          (Tᴴ * P)‖ ^ 2 ≤
          ‖Tᴴ * P - hermitianAverage (gammaAdjoint B C) S n *
            (Tᴴ * P)‖ + 0 := hcapture
      _ ≤ (1 - θ) * ε ^ 2 := by
        rw [add_zero]
        exact hdisp
  have hnormsq : ‖spectralBelow (hermitianAverage (gammaAdjoint B C) S n)
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ *
      (Tᴴ * P)‖ ^ 2 ≤ ε ^ 2 :=
    le_of_mul_le_mul_left hsq hθpos
  have hnn : 0 ≤ ‖spectralBelow (hermitianAverage (gammaAdjoint B C) S n)
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ *
      (Tᴴ * P)‖ := norm_nonneg _
  nlinarith only [hnormsq, hnn, hε.le]

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
          cornerProjection B C S θ n) * movedProjection B C S θ n‖ ≤ ε := by
  intro ε hε
  set ε' : ℝ := min (1 / 2) (ε / 2) with hε'
  have hε'pos : 0 < ε' := lt_min (by norm_num) (half_pos hε)
  have hε'half : ε' ≤ 1 / 2 := min_le_left _ _
  have hε'lt1 : ε' < 1 := lt_of_le_of_lt hε'half (by norm_num)
  obtain ⟨N, hN⟩ := one_sub_moved_mul_corner_vanishing B C θ hQ hone hκ1
    hsymm hgen hθ4 hθ1 ε' hε'pos
  refine ⟨N, fun n hn ↦ ?_⟩
  have hflip := norm_one_sub_mul_flip
    (cornerProjection_isOrthogonalProjection B C S θ n)
    (movedProjection_isOrthogonalProjection B C S θ n)
    (movedProjection_rank B C S θ n).symm hε'pos.le hε'lt1 (hN n hn)
  -- the constant: `ε' / √(1 - ε'²) ≤ 2 ε' ≤ ε`
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt (1 - ε' ^ 2) := by
    have h34 : (1 : ℝ) / 4 ≤ 1 - ε' ^ 2 := by
      nlinarith only [hε'half, hε'pos.le]
    calc
      (1 : ℝ) / 2 = Real.sqrt (1 / 4) := by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt (1 - ε' ^ 2) := Real.sqrt_le_sqrt h34
  have hsqrtpos : 0 < Real.sqrt (1 - ε' ^ 2) :=
    lt_of_lt_of_le (by norm_num) hsqrt
  have hdivbound : ε' / Real.sqrt (1 - ε' ^ 2) ≤ 2 * ε' := by
    rw [div_le_iff₀ hsqrtpos]
    nlinarith only [hsqrt, hε'pos.le]
  calc
    ‖((1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) -
        cornerProjection B C S θ n) * movedProjection B C S θ n‖ ≤
        ε' / Real.sqrt (1 - ε' ^ 2) := hflip
    _ ≤ 2 * ε' := hdivbound
    _ ≤ ε := by
      have := min_le_right (1 / 2 : ℝ) (ε / 2)
      calc
        2 * ε' ≤ 2 * (ε / 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ = ε := by ring

end KazhdanCompressorCorner
end GroupApproximation
