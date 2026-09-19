import GroupApproximation.Sofic.MarkedCompressionSequentialKill

/-!
# Marker-free root capture for Kazhdan compression

The central-involution argument ultimately needs only the following part of
the marked-compression geometry.  The root element `c` centralizes the
Kazhdan image, and conjugation by `t` compresses that image into itself.  In
every operator-norm matrix microstate, the transported root

`d = t * c * t⁻¹`

therefore becomes Hilbert--Schmidt fixed by every element of the Kazhdan
image.  No property of the distinguished marker `a`, and no torsion or
centrality property of the marked word, is used.

This file exposes that reusable interface without changing the already
audited marked-word proof.  `compressionDefect_hsDistSq_vanishing` is the
high-level endpoint used by the finite-normal obstruction.
-/

namespace GroupApproximation
namespace KazhdanCompressorCorner

open Matrix KazhdanCornerMatrices
open scoped ComplexOrder Matrix.Norms.L2Operator commutatorElement

universe u

variable {Gamma : Type} [Group Gamma] {E : Type u} [Group E]

/-! ## Root-vector capture -/

/-- The root lamp vector is asymptotically captured by the finite-stage
Kazhdan projection.  This is the marker-free part of
`commutatorMatrix_hsDistSq_vanishing`. -/
theorem root_capture_vanishing {S : Finset Gamma} {theta : ℝ}
    (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Gamma E)
    (hone : 1 ∈ S) (htheta1 : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      MarkedCompressionVectorChain.vecMass
          ((1 - cornerProjection B C S theta n) *ᵥ
            gammaRowVec B n
              (B.map n C.c : Matrix (B.model n) (B.model n) ℂ)) ≤
        epsilon * Fintype.card (B.model n) := by
  classical
  intro epsilon hepsilon
  have hthetaPos : 0 < 1 - theta := by linarith
  set eta : ℝ := (1 - theta) * epsilon with hetaDef
  have hetaPos : 0 < eta := mul_pos hthetaPos hepsilon
  have hfix : ∀ s ∈ S, ∀ epsilon' : ℝ, 0 < epsilon' → ∃ N, ∀ n ≥ N,
      ‖(B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
        B.map n C.c *
        (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        B.map n C.c‖ ≤ epsilon' := by
    intro s _ epsilon' hepsilon'
    have hconj : C.iota s * C.c * (C.iota s)⁻¹ = C.c := by
      have h := (C.comm_c s).eq
      calc
        C.iota s * C.c * (C.iota s)⁻¹ =
            (C.c * C.iota s) * (C.iota s)⁻¹ := by rw [h]
        _ = C.c := by group
    have h := conj_matrix_defect_vanishing B (C.iota s) C.c
    rw [hconj] at h
    exact h epsilon' hepsilon'
  obtain ⟨N, hN⟩ := eventually_forall_finset S _ hfix hetaPos
  refine ⟨N, fun n hn ↦ ?_⟩
  have hterm : ∀ s ∈ S,
      ‖(B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          B.map n C.c *
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤
        eta := by
    intro s hs
    rw [norm_sub_rev]
    exact hN n hn s hs
  have htermStar : ∀ s ∈ S,
      ‖(B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          B.map n C.c *
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)‖ ≤
        eta := by
    intro s hs
    have hmem := (B.map n (C.iota s)).2
    have hUUstar :
        (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp hmem
      rwa [Matrix.star_eq_conjTranspose] at h
    have hkey :
        (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
              B.map n C.c * B.map n (C.iota s)) *
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ =
        (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          B.map n C.c *
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          B.map n C.c := by
      have hexp :
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n C.c * B.map n (C.iota s)) *
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ =
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n C.c *
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          ((B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
            B.map n C.c *
            ((B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
        noncomm_ring
      rw [hexp, hUUstar, Matrix.one_mul, Matrix.mul_one]
    calc
      ‖(B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            B.map n C.c * B.map n (C.iota s)‖ =
          ‖(B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n C.c * B.map n (C.iota s)) *
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ :=
        (norm_unitary_conjugate hmem).symm
      _ = ‖(B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n C.c *
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
            B.map n C.c‖ := by rw [hkey]
      _ ≤ eta := hN n hn s hs
  have hGnorm : ‖(2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      (((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n C.c *
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            B.map n C.c * B.map n (C.iota s))))‖ ≤ eta := by
    have hsumnorm : ‖∑ s ∈ S,
        (((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
              B.map n C.c *
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
            (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
              B.map n C.c * B.map n (C.iota s)))‖ ≤
        S.card * (2 * eta) := by
      calc
        ‖∑ s ∈ S, _‖ ≤ ∑ s ∈ S, ‖
            ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
                B.map n C.c *
                (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n C.c * B.map n (C.iota s))‖ := norm_sum_le _ _
        _ ≤ ∑ _s ∈ S, 2 * eta := by
          refine Finset.sum_le_sum fun s hs ↦ ?_
          calc
            ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
            _ ≤ 2 * eta := by linarith [hterm s hs, htermStar s hs]
        _ = S.card * (2 * eta) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    rw [norm_smul, norm_smul]
    have hcardC : ‖(S.card : ℂ)⁻¹‖ = (S.card : ℝ)⁻¹ := by
      rw [norm_inv, norm_natCast]
    rw [hcardC]
    norm_num
    have hcardR : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr ⟨1, hone⟩
    calc
      (1 / 2 : ℝ) * ((S.card : ℝ)⁻¹ * ‖∑ s ∈ S,
          (((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
                B.map n C.c *
                (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n C.c * B.map n (C.iota s)))‖) ≤
          (1 / 2 : ℝ) * ((S.card : ℝ)⁻¹ * (S.card * (2 * eta))) := by
        gcongr
      _ = eta := by field_simp [hcardR]
  let H := hermitianAverage (gammaAdjoint B C) S n
  let P := cornerProjection B C S theta n
  let xi : (gammaAdjoint B C).model n → ℂ :=
    gammaRowVec B n
      (B.map n C.c : Matrix (B.model n) (B.model n) ℂ)
  have hHherm : H.IsHermitian :=
    hermitianAverage_conjTranspose (gammaAdjoint B C) S n
  have hHnorm : ‖H‖ ≤ 1 := norm_hermitianAverage_le_one _ S n
  have hresidual :
      ∑ i : (gammaAdjoint B C).model n,
        Complex.normSq ((xi - H *ᵥ xi) i) ≤
        Fintype.card (B.model n) * eta ^ 2 := by
    have hid := lamp_laplacian_matVec B C S hone n
    rw [show xi - H *ᵥ xi =
        gammaRowVec B n ((2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
          (((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
                B.map n C.c *
                (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
            ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
                B.map n C.c * B.map n (C.iota s))))) by exact hid]
    rw [sum_normSq_gammaRowVec]
    exact (sum_normSq_le_card_mul_sq _ _).trans (by gcongr)
  have hxiMass : ∑ i : (gammaAdjoint B C).model n, Complex.normSq (xi i) =
      Fintype.card (B.model n) := by
    rw [show xi = gammaRowVec B n
        (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) by rfl,
      sum_normSq_gammaRowVec]
    exact sum_normSq_of_mem_unitary _ (B.map n C.c).2
  have henergy : (star xi ⬝ᵥ (xi - H *ᵥ xi)).re ≤
      eta * Fintype.card (B.model n) := by
    have hamgm := re_star_dotProduct_le hetaPos xi (xi - H *ᵥ xi)
    rw [hxiMass] at hamgm
    calc
      (star xi ⬝ᵥ (xi - H *ᵥ xi)).re ≤
          (2 : ℝ)⁻¹ * (eta * Fintype.card (B.model n) + eta⁻¹ *
            ∑ i : (gammaAdjoint B C).model n,
              Complex.normSq ((xi - H *ᵥ xi) i)) := hamgm
      _ ≤ (2 : ℝ)⁻¹ * (eta * Fintype.card (B.model n) + eta⁻¹ *
            (Fintype.card (B.model n) * eta ^ 2)) := by gcongr
      _ = eta * Fintype.card (B.model n) := by field_simp; ring
  have hcaptureRaw := capture_vec H hHherm theta 0 htheta1.le (by positivity)
    (by simpa using hHnorm) xi
  have hbelow : spectralBelow H hHherm theta = 1 - P := by rfl
  rw [hbelow, zero_mul, add_zero] at hcaptureRaw
  rw [MarkedCompressionVectorChain.vecMass]
  change ∑ i : (gammaAdjoint B C).model n,
      Complex.normSq (((1 - P) *ᵥ xi) i) ≤ _
  have hscaled : (1 - theta) * ∑ i : (gammaAdjoint B C).model n,
      Complex.normSq (((1 - P) *ᵥ xi) i) ≤
      eta * Fintype.card (B.model n) := hcaptureRaw.trans henergy
  rw [hetaDef] at hscaled
  nlinarith

/-! ## Transported-root displacement -/

/-- The matrix representing `t c t⁻¹` becomes Hilbert--Schmidt fixed by
an arbitrary element of the Kazhdan image. -/
theorem transportedRoot_displacement_hsDistSq_vanishing
    (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Gamma E) (gamma : Gamma) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        ((B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        (lampMatrix B C n) ≤ epsilon := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappaPos, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair
      C.kazhdan
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hgap : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) :=
    div_pos (sq_pos_of_pos hkappaPos) (mul_pos (by norm_num) hcard)
  let c0 : ℝ := 1 - kappa ^ 2 / (4 * S.card)
  let theta : ℝ := (c0 + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [c0, theta]
    linarith
  have htheta1 : theta < 1 := by
    dsimp [c0, theta]
    linarith
  intro epsilon hepsilon
  have heFix : 0 < epsilon / 6 := by linarith
  have heReverse : 0 < epsilon / 48 := by linarith
  obtain ⟨N1, hN1⟩ := displacement_vanishing B C theta hpair hone hkappaOne
    hsymm hgen htheta4 gamma (Real.sqrt (epsilon / 6))
      (Real.sqrt_pos.mpr heFix)
  obtain ⟨N2, hN2⟩ := one_sub_corner_mul_moved_vanishing B C theta hpair
    hone hkappaOne hsymm hgen htheta4 htheta1
      (Real.sqrt (epsilon / 48)) (Real.sqrt_pos.mpr heReverse)
  obtain ⟨N3, hN3⟩ := root_capture_vanishing B C hone htheta1
    (epsilon / 48) heReverse
  refine ⟨max N1 (max N2 N3), fun n hn ↦ ?_⟩
  have hn1 : n ≥ N1 := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N2 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : n ≥ N3 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hstage := MarkedCompressionVectorChain.conjugated_transport_hsDistSq_le
    (B.modelNonempty n) (B.map n (C.iota gamma)).2 (B.map n C.t).2
    (B.map n C.c).2 (cornerProjection_isOrthogonalProjection B C S theta n)
    (hN1 n hn1) (hN2 n hn2) (hN3 n hn3)
  have hsqrtFix : (Real.sqrt (epsilon / 6)) ^ 2 = epsilon / 6 :=
    Real.sq_sqrt heFix.le
  have hsqrtReverse : (Real.sqrt (epsilon / 48)) ^ 2 = epsilon / 48 :=
    Real.sq_sqrt heReverse.le
  have hstage' :
      hsDistSq (B.model n)
        ((B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        (lampMatrix B C n) ≤
      2 * (Real.sqrt (epsilon / 6)) ^ 2 +
        16 * (Real.sqrt (epsilon / 48)) ^ 2 + 16 * (epsilon / 48) := by
    simpa [lampMatrix, gammaAdjoint,
      OpAlmostRepresentation.adjoint_map] using hstage
  rw [hsqrtFix, hsqrtReverse] at hstage'
  linarith

/-! ## Translation to the exact group commutator -/

/-- Conjugating the transported-lamp matrix by an arbitrary Kazhdan element
tracks conjugation of the corresponding group element. -/
theorem conjugatedLampGamma_defect_vanishing
    (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Gamma E) (gamma : Gamma) :
    OpNormVanishing B (fun n ↦
      (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        B.map n (C.iota gamma * (C.t * C.c * C.t⁻¹) *
          (C.iota gamma)⁻¹)) := by
  have hb : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun h n ↦ norm_le_one_of_mem_unitary (B.map n h).2
  have hbstar : ∀ (h : E) (n : ℕ),
      ‖(B.map n h : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤ 1 := by
    intro h n
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hb h n
  have h1 : OpNormVanishing B (fun n ↦
      (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
        (lampMatrix B C n - B.map n (C.t * C.c * C.t⁻¹)) *
        (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
    ((lampMatrix_defect_vanishing B C).mul_left_of_norm_le_one _
      (hb (C.iota gamma))).mul_right_of_norm_le_one _ (hbstar (C.iota gamma))
  have h2 := conj_matrix_defect_vanishing B (C.iota gamma)
    (C.t * C.c * C.t⁻¹)
  refine (h1.add h2).congr fun n ↦ ?_
  noncomm_ring

/-- A product with an inverse is tracked by the product of a microstate and
the adjoint of the other microstate. -/
theorem productInverse_defect_vanishing (B : OpAlmostRepresentation E)
    (x y : E) :
    OpNormVanishing B (fun n ↦
      (B.map n x : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n y : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        B.map n (x * y⁻¹)) := by
  have hx : ∀ n,
      ‖(B.map n x : Matrix (B.model n) (B.model n) ℂ)‖ ≤ 1 :=
    fun n ↦ norm_le_one_of_mem_unitary (B.map n x).2
  have hInv := (map_inv_vanishing B y).neg
  have h1 := hInv.mul_left_of_norm_le_one
    (fun n ↦ (B.map n x : Matrix (B.model n) (B.model n) ℂ)) hx
  have h2 := (multiplicativeDefect_vanishing B x y⁻¹).neg
  refine (h1.add h2).congr fun n ↦ ?_
  noncomm_ring

/-- **Marker-free Kazhdan-compression collapse, with the transport step as an
input.**  Everything after the transport step is operator-norm bookkeeping and
does not care how the transported root displacement was obtained, so the step
is taken as a hypothesis and the two routes to it share this proof instead of
duplicating the estimate combination that follows.

`compressionDefect_hsDistSq_vanishing` below supplies the Appendix-B step;
`Sofic/LiteralRouteTransport.lean` supplies the printed Section-3 one. -/
theorem compressionDefect_hsDistSq_vanishing_of
    (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Gamma E) (gamma : Gamma)
    (htransport : ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        ((B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        (lampMatrix B C n) ≤ epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        (B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆)
        (B.map n 1) ≤ epsilon := by
  classical
  let x : E := C.t * C.c * C.t⁻¹
  let y : E := C.iota gamma * x * (C.iota gamma)⁻¹
  intro epsilon hepsilon
  have heSmall : 0 < epsilon / 128 := by linarith
  obtain ⟨N1, hN1⟩ := htransport (epsilon / 128) heSmall
  obtain ⟨N2, hN2⟩ := lampMatrix_defect_vanishing B C
    (Real.sqrt (epsilon / 128)) (Real.sqrt_pos.mpr heSmall)
  obtain ⟨N3, hN3⟩ := conjugatedLampGamma_defect_vanishing B C gamma
    (Real.sqrt (epsilon / 128)) (Real.sqrt_pos.mpr heSmall)
  obtain ⟨N4, hN4⟩ := productInverse_defect_vanishing B x y
    (Real.sqrt (epsilon / 64)) (Real.sqrt_pos.mpr (by linarith))
  obtain ⟨N5, hN5⟩ := map_one_vanishing B
    (Real.sqrt (epsilon / 64)) (Real.sqrt_pos.mpr (by linarith))
  refine ⟨max N1 (max N2 (max N3 (max N4 N5))), fun n hn ↦ ?_⟩
  have hn1 : n ≥ N1 := (le_max_left _ _).trans hn
  have hn2 : n ≥ N2 :=
    (le_max_left N2 (max N3 (max N4 N5))).trans
      ((le_max_right N1 (max N2 (max N3 (max N4 N5)))).trans hn)
  have hn3 : n ≥ N3 :=
    (le_max_left N3 (max N4 N5)).trans
      ((le_max_right N2 (max N3 (max N4 N5))).trans
        ((le_max_right N1 (max N2 (max N3 (max N4 N5)))).trans hn))
  have hn4 : n ≥ N4 :=
    (le_max_left N4 N5).trans
      ((le_max_right N3 (max N4 N5)).trans
        ((le_max_right N2 (max N3 (max N4 N5))).trans
          ((le_max_right N1 (max N2 (max N3 (max N4 N5)))).trans hn)))
  have hn5 : n ≥ N5 :=
    (le_max_right N4 N5).trans
      ((le_max_right N3 (max N4 N5)).trans
        ((le_max_right N2 (max N3 (max N4 N5))).trans
          ((le_max_right N1 (max N2 (max N3 (max N4 N5)))).trans hn)))
  let Dm : Matrix (B.model n) (B.model n) ℂ := lampMatrix B C n
  let Em : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ) * Dm *
      (B.map n (C.iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ
  let Ux : Matrix (B.model n) (B.model n) ℂ := B.map n x
  let Uy : Matrix (B.model n) (B.model n) ℂ := B.map n y
  let Pm : Matrix (B.model n) (B.model n) ℂ := Ux * Uyᴴ
  have hDmEm : hsDistSq (B.model n) Em Dm ≤ epsilon / 128 := by
    simpa [Dm, Em] using hN1 n hn1
  have hDmUx : hsDistSq (B.model n) Dm Ux ≤ epsilon / 128 := by
    exact (hsDistSq_le_sq_l2_opNorm _ _ _).trans (by
      have h : ‖Dm - Ux‖ ≤ Real.sqrt (epsilon / 128) := by
        simpa [Dm, Ux, x] using hN2 n hn2
      have hsqrt : (Real.sqrt (epsilon / 128)) ^ 2 = epsilon / 128 :=
        Real.sq_sqrt heSmall.le
      nlinarith [norm_nonneg (Dm - Ux)])
  have hEmUy : hsDistSq (B.model n) Em Uy ≤ epsilon / 128 := by
    exact (hsDistSq_le_sq_l2_opNorm _ _ _).trans (by
      have h : ‖Em - Uy‖ ≤ Real.sqrt (epsilon / 128) := by
        simpa [Em, Dm, Uy, y, x] using hN3 n hn3
      have hsqrt : (Real.sqrt (epsilon / 128)) ^ 2 = epsilon / 128 :=
        Real.sq_sqrt heSmall.le
      nlinarith [norm_nonneg (Em - Uy)])
  have hUyUx : hsDistSq (B.model n) Uy Ux ≤ 10 * (epsilon / 128) := by
    have hfirst := hsDistSq_le_two_add_two (B.model n) Uy Dm Em
    have hsecond := hsDistSq_le_two_add_two (B.model n) Uy Ux Dm
    have hUyEm : hsDistSq (B.model n) Uy Em ≤ epsilon / 128 := by
      rw [hsDistSq_comm]
      exact hEmUy
    have hEmDm : hsDistSq (B.model n) Em Dm ≤ epsilon / 128 := by
      exact hDmEm
    linarith [hfirst, hsecond, hDmUx, hUyEm, hEmDm]
  have hPm : hsDistSq (B.model n) Pm 1 ≤ 10 * (epsilon / 128) := by
    have hUyStar : Uy * Uyᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp (B.map n y).2
      simpa [Uy, Matrix.star_eq_conjTranspose] using h
    have hfactor : Pm - 1 = (Ux - Uy) * Uyᴴ := by
      dsimp [Pm]
      rw [Matrix.sub_mul, hUyStar]
    change hsNormSq (B.model n) (Pm - 1) ≤ _
    rw [hfactor, hsNormSq_mul_right (B.model n)
      (conjTranspose_mem_unitaryGroup (B.map n y).2)]
    change hsDistSq (B.model n) Ux Uy ≤ _
    rw [hsDistSq_comm]
    exact hUyUx
  have hwordEq : x * y⁻¹ = ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆ := by
    dsimp [x, y]
    rw [commutatorElement_def]
    group
  have hdef : hsDistSq (B.model n) Pm
      (B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) ≤ epsilon / 64 := by
    exact (hsDistSq_le_sq_l2_opNorm _ _ _).trans (by
      have h := hN4 n hn4
      rw [hwordEq] at h
      have hop : ‖Pm -
          B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆‖ ≤
          Real.sqrt (epsilon / 64) := by
        simpa [Pm, Ux, Uy] using h
      have hsqrt : (Real.sqrt (epsilon / 64)) ^ 2 = epsilon / 64 :=
        Real.sq_sqrt (by linarith)
      nlinarith [norm_nonneg
        (Pm - B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆)])
  have hone : hsDistSq (B.model n) (1 : Matrix (B.model n) (B.model n) ℂ)
      (B.map n 1) ≤ epsilon / 64 := by
    exact (hsDistSq_le_sq_l2_opNorm _ _ _).trans (by
      have h := hN5 n hn5
      have hop : ‖(1 : Matrix (B.model n) (B.model n) ℂ) - B.map n 1‖ ≤
          Real.sqrt (epsilon / 64) := by
        rw [norm_sub_rev]
        exact h
      have hsqrt : (Real.sqrt (epsilon / 64)) ^ 2 = epsilon / 64 :=
        Real.sq_sqrt (by linarith)
      nlinarith [norm_nonneg
        ((1 : Matrix (B.model n) (B.model n) ℂ) - B.map n 1)])
  have htri1 := hsDistSq_le_two_add_two (B.model n)
    (B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) 1 Pm
  have htri2 := hsDistSq_le_two_add_two (B.model n)
    (B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) (B.map n 1) 1
  rw [hsDistSq_comm (B.model n)
    (B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) Pm] at htri1
  linarith [htri1, htri2, hPm, hdef, hone]

/-- **Marker-free Kazhdan-compression collapse.**  Every pointwise
compression defect `[t c t⁻¹, iota gamma]` is Hilbert--Schmidt trivial in
every operator-norm almost representation.

Statement and consumers are unchanged; the proof now names the transport step
it uses, which is the Appendix-B one.  Rows `INT.03` and `INT.04` are about
that choice, and the alternative is
`UltraproductRigidityRoute.compressionDefect_hsDistSq_vanishing_literal`,
which proves this same statement through `\ref{thm:kazhdan-transport}`.

That name is corrected, not renamed: this sentence used to promise the
alternative as `KazhdanAsymptoticCommutant.compressionDefect_hsDistSq_vanishing_literal`,
and no such declaration existed anywhere in the corpus.  It lives in
`Analysis/UltraproductRigidityRoute` because the printed route is only
available below that module, and it could not be named here in any case --
this file is one of that module's imports, so the exchange has to happen
downstream rather than in place. -/
theorem compressionDefect_hsDistSq_vanishing
    (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Gamma E) (gamma : Gamma) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        (B.map n ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆)
        (B.map n 1) ≤ epsilon :=
  compressionDefect_hsDistSq_vanishing_of B C gamma
    (transportedRoot_displacement_hsDistSq_vanishing B C gamma)

end KazhdanCompressorCorner
end GroupApproximation
