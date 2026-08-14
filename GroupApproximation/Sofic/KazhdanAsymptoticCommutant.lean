import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Sofic.MarkedCompressionRootCapture

/-!
# Kazhdan transport of asymptotic commutants

This is the sequence-valued form of the compressor argument.  A one-sided
compressor of a Kazhdan image preserves its entire normalized
Hilbert--Schmidt asymptotic commutant in every operator-norm almost
representation.  No distinguished lamp, endomorphism, torsion element, or
marked word occurs in the statement.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator

variable {Γ E : Type} [Group Γ] [Group E]

/-- Squared normalized Hilbert--Schmidt convergence to zero. -/
def HSSqVanishing (B : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, hsNormSq (B.model n) (x n) ≤ ε

theorem HSSqVanishing.congr {B : OpAlmostRepresentation E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) (hxy : ∀ n, x n = y n) :
    HSSqVanishing B y := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn ↦ by rw [← hxy n]; exact hN n hn⟩

theorem HSSqVanishing.neg {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) : HSSqVanishing B (fun n ↦ -x n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnorm : hsNormSq (B.model n) (-x n) = hsNormSq (B.model n) (x n) := by
    rw [show -x n = (-1 : ℂ) • x n by simp, hsNormSq_smul]
    norm_num
  rw [hnorm]
  exact hN n hn

theorem HSSqVanishing.add {B : OpAlmostRepresentation E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) (hy : HSSqVanishing B y) :
    HSSqVanishing B (fun n ↦ x n + y n) := by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 4) (by linarith)
  obtain ⟨Ny, hNy⟩ := hy (ε / 4) (by linarith)
  refine ⟨max Nx Ny, fun n hn ↦ ?_⟩
  exact (hsNormSq_add_le (B.model n) (x n) (y n)).trans (by
    have hx' := hNx n ((le_max_left _ _).trans hn)
    have hy' := hNy n ((le_max_right _ _).trans hn)
    linarith)

theorem HSSqVanishing.smul {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x) (c : ℂ) :
    HSSqVanishing B (fun n ↦ c • x n) := by
  intro ε hε
  have hden : 0 < Complex.normSq c + 1 := by positivity
  obtain ⟨N, hN⟩ := hx (ε / (Complex.normSq c + 1)) (div_pos hε hden)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hsNormSq_smul]
  calc
    Complex.normSq c * hsNormSq (B.model n) (x n) ≤
        Complex.normSq c * (ε / (Complex.normSq c + 1)) :=
      mul_le_mul_of_nonneg_left (hN n hn) (Complex.normSq_nonneg c)
    _ ≤ ε := by
      rw [div_le_iff₀ hden]
      nlinarith [Complex.normSq_nonneg c]

theorem HSSqVanishing.finset_sum {B : OpAlmostRepresentation E}
    {I : Type} (s : Finset I)
    (x : I → ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ i ∈ s, HSSqVanishing B (x i)) :
    HSSqVanishing B (fun n ↦ ∑ i ∈ s, x i n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      exact ⟨0, fun n _ ↦ by simp [hsNormSq, hε.le]⟩
  | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (hx i (Finset.mem_insert_self i s)).add
          (ih fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

theorem HSSqVanishing.unitary_conjugate
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : HSSqVanishing B x)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) :
    HSSqVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hsNormSq_mul_right _ (conjTranspose_mem_unitaryGroup (u n).2),
    hsNormSq_mul_left _ (u n).2 (B.modelNonempty n)]
  exact hN n hn

/-- Operator-norm null sequences are normalized-Hilbert--Schmidt null. -/
theorem HSSqVanishing.of_opNormVanishing
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : OpNormVanishing B x) : HSSqVanishing B x := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hx (Real.sqrt epsilon) (Real.sqrt_pos.2 hepsilon)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hdom := hsDistSq_le_sq_l2_opNorm (B.model n) (x n) 0
  rw [hsDistSq, sub_zero] at hdom
  calc
    hsNormSq (B.model n) (x n) ≤ ‖x n‖ ^ 2 := hdom
    _ ≤ (Real.sqrt epsilon) ^ 2 := by
      nlinarith [norm_nonneg (x n), Real.sqrt_nonneg epsilon, hN n hn]
    _ = epsilon := Real.sq_sqrt hepsilon.le

/-- A matrix sequence asymptotically centralizes the image of a homomorphism. -/
def IsAsymptoticCommutantOf (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ γ : Γ, HSSqVanishing B (fun n ↦
    x n - (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
      x n * (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)

/-- A bounded matrix sequence asymptotically centralizes the Kazhdan image. -/
abbrev IsAsymptoticCommutant (B : OpAlmostRepresentation E)
    (C : KazhdanCompressionCore Γ E) := IsAsymptoticCommutantOf B C.iota

/-- Uniform operator-norm boundedness of a matrix sequence. -/
def IsUniformlyBounded (B : OpAlmostRepresentation E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M

/-- Exact unitary conjugation preserves uniform boundedness. -/
theorem IsUniformlyBounded.unitary_conjugate
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsUniformlyBounded B x)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) :
    IsUniformlyBounded B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  obtain ⟨M, hM, hMx⟩ := hx
  refine ⟨M, hM, fun n ↦ ?_⟩
  rw [CStarRing.norm_mem_unitary_mul _ (u n).2,
    CStarRing.norm_mul_mem_unitary _ (conjTranspose_mem_unitaryGroup (u n).2)]
  exact hMx n

/-- Hilbert--Schmidt-equivalent bounded sequences have the same asymptotic
commutation relations. -/
theorem IsAsymptoticCommutant.congr_hs
    {B : OpAlmostRepresentation E} {C : KazhdanCompressionCore Γ E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x)
    (hxy : HSSqVanishing B (fun n ↦ x n - y n)) :
    IsAsymptoticCommutant B C y := by
  intro gamma
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ :=
    fun n ↦ B.map n (C.iota gamma)
  have hconj := hxy.unitary_conjugate u
  exact ((hx gamma).add hxy.neg |>.add hconj).congr fun n ↦ by
    have hu : (u n : Matrix (B.model n) (B.model n) ℂ) *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem (u n).2
    simp only [u]
    noncomm_ring [hu]

/-- Conjugating the reverse displacement by the implementing unitary turns it
into the negative forward displacement. -/
theorem reverse_hsSqVanishing
    {B : OpAlmostRepresentation E}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x) (γ : Γ) :
    HSSqVanishing B (fun n ↦
      x n - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        x n * B.map n (C.iota γ)) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n (C.iota γ)
  have h := (hx γ).neg.unitary_conjugate (fun n ↦
    ⟨(u n : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (u n).2⟩)
  exact h.congr fun n ↦ by
    have huu : (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ * u n = 1 :=
      Unitary.star_mul_self_of_mem (u n).2
    have huuh : (u n : Matrix (B.model n) (B.model n) ℂ) *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem (u n).2
    simp only [u]
    noncomm_ring [huu, huuh]

/-- The Hermitian Kazhdan-average residual of an asymptotic-commutant
sequence is Hilbert--Schmidt null. -/
theorem laplacian_hsSqVanishing
    {B : OpAlmostRepresentation E}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x)
    (S : Finset Γ) (hone : 1 ∈ S) :
    HSSqVanishing B (fun n ↦
      (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            x n * B.map n (C.iota s))))) := by
  have hsum : HSSqVanishing B (fun n ↦ ∑ s ∈ S,
      ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          x n * B.map n (C.iota s)))) := by
    apply HSSqVanishing.finset_sum S
    intro s _
    exact (hx s).add (reverse_hsSqVanishing hx s)
  exact (hsum.smul (S.card : ℂ)⁻¹).smul (2 : ℂ)⁻¹

/-- Spectral capture for every bounded asymptotic-commutant sequence. -/
theorem capture_vanishing
    {B : OpAlmostRepresentation E}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x)
    {S : Finset Γ} (hone : 1 ∈ S) {θ : ℝ} (hθ : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      MarkedCompressionVectorChain.vecMass
        ((1 - cornerProjection B C S θ n) *ᵥ gammaRowVec B n (x n)) ≤
          ε * Fintype.card (B.model n) := by
  classical
  obtain ⟨M, hM, hMx⟩ := hbound
  intro ε hε
  have hgap : 0 < 1 - θ := by linarith
  let η : ℝ := (1 - θ) * ε / (M ^ 2 + 1)
  have hden : 0 < M ^ 2 + 1 := by positivity
  have hη : 0 < η := div_pos (mul_pos hgap hε) hden
  obtain ⟨N, hN⟩ := laplacian_hsSqVanishing hx S hone (η ^ 2) (sq_pos_of_pos hη)
  refine ⟨N, fun n hn ↦ ?_⟩
  let R : Matrix (B.model n) (B.model n) ℂ :=
    (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          x n * B.map n (C.iota s))))
  let H := hermitianAverage (gammaAdjoint B C) S n
  let P := cornerProjection B C S θ n
  let ξ := gammaRowVec B n (x n)
  have hresidVec : ξ - H *ᵥ ξ = gammaRowVec B n R := by
    simpa [R, H, ξ] using matrix_laplacian_matVec B C S hone n (x n)
  have hR : hsNormSq (B.model n) R ≤ η ^ 2 := by
    simpa [R] using hN n hn
  have hcard : (0 : ℝ) < Fintype.card (B.model n) := by
    exact_mod_cast B.modelNonempty n
  have hresidMass :
      ∑ i : (gammaAdjoint B C).model n,
          Complex.normSq ((ξ - H *ᵥ ξ) i) ≤
        Fintype.card (B.model n) * η ^ 2 := by
    rw [hresidVec, sum_normSq_gammaRowVec]
    unfold hsNormSq at hR
    rw [div_le_iff₀ hcard] at hR
    simpa [mul_comm] using hR
  have hxiMass :
      ∑ i : (gammaAdjoint B C).model n, Complex.normSq (ξ i) ≤
        Fintype.card (B.model n) * M ^ 2 := by
    rw [show ξ = gammaRowVec B n (x n) by rfl, sum_normSq_gammaRowVec]
    exact (sum_normSq_le_card_mul_sq _ _).trans (by gcongr; exact hMx n)
  have henergy : (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
      ((1 - θ) * ε) * Fintype.card (B.model n) := by
    have hamgm := re_star_dotProduct_le hη ξ (ξ - H *ᵥ ξ)
    calc
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
          (2 : ℝ)⁻¹ *
            (η * ∑ i, Complex.normSq (ξ i) +
              η⁻¹ * ∑ i, Complex.normSq ((ξ - H *ᵥ ξ) i)) := hamgm
      _ ≤ (2 : ℝ)⁻¹ *
            (η * (Fintype.card (B.model n) * M ^ 2) +
              η⁻¹ * (Fintype.card (B.model n) * η ^ 2)) := by gcongr
      _ ≤ ((1 - θ) * ε) * Fintype.card (B.model n) := by
        dsimp [η]
        field_simp
        nlinarith [sq_nonneg M]
  have hcapture := capture_vec H
    (by simpa [H] using
      hermitianAverage_conjTranspose (gammaAdjoint B C) S n)
    θ 0 hθ.le (by positivity)
    (by simpa [H] using norm_hermitianAverage_le_one (gammaAdjoint B C) S n) ξ
  have hbelow : spectralBelow H
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ = 1 - P := rfl
  rw [hbelow, zero_mul, add_zero] at hcapture
  have hmul : (1 - θ) *
      MarkedCompressionVectorChain.vecMass ((1 - P) *ᵥ ξ) ≤
        (1 - θ) * (ε * Fintype.card (B.model n)) :=
    hcapture.trans (by simpa [mul_assoc] using henergy)
  exact le_of_mul_le_mul_left hmul hgap

private theorem transport_of_leakage
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x)
    (S : Finset Γ) (kappa theta : ℝ)
    (hone : 1 ∈ S) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hkappaOne : kappa ≤ 1)
    (hpair : IsKazhdanPair.{0, 0} Γ S kappa)
    (htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta)
    (htheta1 : theta < 1)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (hleak : ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      ‖(1 - cornerProjection B C S theta n) *
        (conjDouble (u n) * cornerProjection B C S theta n *
          (conjDouble (u n))ᴴ)‖ ≤ epsilon) :
    IsAsymptoticCommutant B C (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  classical
  obtain ⟨M, hM, hMx⟩ := hbound
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  intro γ ε hε
  let q : ℝ := min 1 (ε / (40 * (M ^ 2 + 1)))
  have hden : 0 < 40 * (M ^ 2 + 1) := by positivity
  have hq : 0 < q := lt_min (by norm_num) (div_pos hε hden)
  obtain ⟨Nfix, hNfix⟩ := displacement_vanishing B C theta hpair hone hkappaOne
    hsymm hgen htheta4 γ q hq
  obtain ⟨Nrev, hNrev⟩ := hleak q hq
  obtain ⟨Ncap, hNcap⟩ := capture_vanishing hx ⟨M, hM, hMx⟩ hone htheta1 q hq
  refine ⟨max Nfix (max Nrev Ncap), fun n hn ↦ ?_⟩
  let Ua : Matrix (B.model n) (B.model n) ℂ := B.map n (C.iota γ)
  let Ut : Matrix (B.model n) (B.model n) ℂ := u n
  let X : Matrix (B.model n) (B.model n) ℂ := x n
  let P := cornerProjection B C S theta n
  have hfix : ‖(conjDouble Ua - 1) * P‖ ≤ q := by
    simpa [Ua, P, gammaAdjoint] using
      hNfix n ((le_max_left _ _).trans hn)
  have hrev : ‖(1 - P) * (conjDouble Ut * P * (conjDouble Ut)ᴴ)‖ ≤ q := by
    simpa [P, Ut] using
      hNrev n ((le_max_left _ _).trans (le_max_right _ _).trans hn)
  have hcap := hNcap n ((le_max_right _ _).trans (le_max_right _ _).trans hn)
  have hchain := MarkedCompressionVectorChain.transported_displacement_le
    (Y := doubleModel (B.model n)) (by rw [card_doubleModel]; positivity)
    (cornerProjection_isOrthogonalProjection B C S theta n)
    (conjDouble_mem_unitaryGroup (u n).2)
    (conjDouble_mem_unitaryGroup (B.map n (C.iota γ)).2)
    hfix hrev hcap
  have hxmass : MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) ≤
      Fintype.card (B.model n) * M ^ 2 := by
    rw [MarkedCompressionVectorChain.vecMass, sum_normSq_gammaRowVec]
    exact (sum_normSq_le_card_mul_sq _ _).trans (by gcongr; exact hMx n)
  have hqone : q ≤ 1 := min_le_left _ _
  have hqeps : q * (40 * (M ^ 2 + 1)) ≤ ε := by
    calc
      q * (40 * (M ^ 2 + 1)) ≤
          (ε / (40 * (M ^ 2 + 1))) * (40 * (M ^ 2 + 1)) := by
        gcongr
        exact min_le_right _ _
      _ = ε := by field_simp
  have hmass :
      MarkedCompressionVectorChain.vecMass
        (conjDouble Ua *ᵥ (conjDouble Ut *ᵥ gammaRowVec B n X) -
          conjDouble Ut *ᵥ gammaRowVec B n X) ≤
        (2 * q ^ 2 + 16 * q ^ 2) *
            MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) +
          16 * (q * Fintype.card (B.model n)) :=
    hchain
  have hmass' :
      MarkedCompressionVectorChain.vecMass
        (conjDouble Ua *ᵥ (conjDouble Ut *ᵥ gammaRowVec B n X) -
          conjDouble Ut *ᵥ gammaRowVec B n X) ≤
        Fintype.card (B.model n) *
          (18 * q ^ 2 * M ^ 2 + 16 * q) := by
    calc
      _ ≤ (2 * q ^ 2 + 16 * q ^ 2) *
            MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) +
          16 * (q * Fintype.card (B.model n)) := hmass
      _ ≤ (2 * q ^ 2 + 16 * q ^ 2) *
            (Fintype.card (B.model n) * M ^ 2) +
          16 * (q * Fintype.card (B.model n)) := by gcongr
      _ = Fintype.card (B.model n) *
          (18 * q ^ 2 * M ^ 2 + 16 * q) := by ring
  have hsmall : 18 * q ^ 2 * M ^ 2 + 16 * q ≤ ε := by
    calc
      18 * q ^ 2 * M ^ 2 + 16 * q ≤
          q * (40 * (M ^ 2 + 1)) := by
        nlinarith [hM, hq.le, hqone, sq_nonneg M,
          mul_nonneg hq.le (sq_nonneg M)]
      _ ≤ ε := hqeps
  have hcardR : (0 : ℝ) < Fintype.card (B.model n) := by
    exact_mod_cast B.modelNonempty n
  change hsNormSq (B.model n)
      (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) ≤ ε
  rw [hsNormSq]
  rw [div_le_iff₀ hcardR]
  calc
    (∑ i : B.model n, ∑ j : B.model n,
        Complex.normSq
          ((Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) i j)) =
        MarkedCompressionVectorChain.vecMass
          (conjDouble Ua *ᵥ (conjDouble Ut *ᵥ gammaRowVec B n X) -
            conjDouble Ut *ᵥ gammaRowVec B n X) := by
      rw [conjDouble_mulVec_rowVec, conjDouble_mulVec_rowVec,
        MarkedCompressionVectorChain.vecMass, sum_normSq_rowVec]
      refine Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) i j =
          -((Ua * (Ut * X * Utᴴ) * Uaᴴ - Ut * X * Utᴴ) i j) by
            simp; ring,
        Complex.normSq_neg]
    _ ≤ Fintype.card (B.model n) *
        (18 * q ^ 2 * M ^ 2 + 16 * q) := hmass'
    _ ≤ Fintype.card (B.model n) * ε :=
      mul_le_mul_of_nonneg_left hsmall hcardR.le

/-- **Forward Kazhdan transport.**  A one-sided compressor preserves every
uniformly bounded normalized-Hilbert--Schmidt asymptotic commutant sequence. -/
theorem transport
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair C.kazhdan
  let theta : ℝ := ((1 - kappa ^ 2 / (4 * S.card)) + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [theta]
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  apply transport_of_leakage B C x hx hbound S kappa theta hone hsymm hgen
    hkappaOne hpair htheta4 htheta1 (fun n ↦ B.map n C.t)
  intro epsilon hepsilon
  simpa [movedProjection] using
    one_sub_corner_mul_moved_vanishing B C theta hpair hone hkappaOne
      hsymm hgen htheta4 htheta1 epsilon hepsilon

/-- **Reverse Kazhdan transport.**  Finite-coordinate rank balance upgrades
the one-sided compressor to invariance under the inverse adjoint action. -/
theorem transport_star
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, _hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair C.kazhdan
  let theta : ℝ := ((1 - kappa ^ 2 / (4 * S.card)) + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [theta]
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  apply transport_of_leakage B C x hx hbound S kappa theta hone hsymm hgen
    hkappaOne hpair htheta4 htheta1 (fun n ↦
      ⟨(B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ,
        conjTranspose_mem_unitaryGroup (B.map n C.t).2⟩)
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := one_sub_moved_mul_corner_vanishing B C theta hpair
    hone hkappaOne hsymm hgen htheta4 htheta1 epsilon hepsilon
  refine ⟨N, fun n hn ↦ ?_⟩
  let T : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    conjDouble (B.map n C.t)
  let P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    cornerProjection B C S theta n
  have hT : T ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
    conjDouble_mem_unitaryGroup (B.map n C.t).2
  have hTstar : Tᴴ ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
    conjTranspose_mem_unitaryGroup hT
  have hTTstar : T * Tᴴ = 1 := Unitary.mul_star_self_of_mem hT
  have hTstarT : Tᴴ * T = 1 := Unitary.star_mul_self_of_mem hT
  have hraw : ‖(1 - T * P * Tᴴ) * P‖ ≤ epsilon := by
    simpa [T, P, movedProjection] using hN n hn
  have hfactor :
      (1 - P) * (Tᴴ * P * T) = Tᴴ * ((1 - T * P * Tᴴ) * P) * T := by
    noncomm_ring [hTTstar, hTstarT]
  have htarget : ‖(1 - P) * (Tᴴ * P * T)‖ ≤ epsilon := by
    rw [hfactor, CStarRing.norm_mem_unitary_mul _ hTstar,
      CStarRing.norm_mul_mem_unitary _ hT]
    exact hraw
  simpa [T, P, conjDouble_conjTranspose] using htarget

/-- A one-sided compressor acts as a two-sided symmetry of the bounded
normalized-Hilbert--Schmidt asymptotic commutant. -/
theorem transport_both
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
  ⟨transport B C x hx hbound, transport_star B C x hx hbound⟩

/-- The compression core attached to an arbitrary one-sided compressor.  The
root is irrelevant for asymptotic-commutant transport and is chosen to be the
identity. -/
def coreOfCompressor (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (s : E) (hs : s ∈ compressionSet iota.range) : KazhdanCompressionCore Γ E where
  iota := iota
  t := s
  c := 1
  kazhdan := hkazhdan
  compresses gamma := by
    obtain ⟨delta, hdelta⟩ := hs (iota gamma) ⟨gamma, rfl⟩
    exact ⟨delta, hdelta⟩
  comm_c gamma := one_comm _

/-- Every one-sided compressor, not merely a distinguished stable letter,
acts in both directions on the bounded asymptotic commutant. -/
theorem compressionSet_transport_both
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ gamma : Γ, HSSqVanishing B (fun n ↦
      x n - (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
        x n * (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ))
    (hbound : IsUniformlyBounded B x)
    {s : E} (hs : s ∈ compressionSet iota.range) :
    (∀ gamma : Γ, HSSqVanishing B (fun n ↦
      (B.map n s : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n s : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ)) ∧
    (∀ gamma : Γ, HSSqVanishing B (fun n ↦
      (B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n * B.map n s -
        (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n s : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n * B.map n s) *
          (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ)) := by
  let C := coreOfCompressor iota hkazhdan s hs
  have htransport := transport_both B C x (by simpa [IsAsymptoticCommutant, C] using hx)
    hbound
  simpa [IsAsymptoticCommutant, C] using htransport

end KazhdanAsymptoticCommutant
end GroupApproximation
