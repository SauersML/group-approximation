import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.ApproxInvolutionCorner
import GroupApproximation.Sofic.KazhdanCornerPolar

/-!
# An MF regular character forces the group to be operator MF

The definitional surface of Shulman's MF-trace condition, specialized to
the regular character of a countable group, and the recognition theorem:
if the regular character admits matrix models that are asymptotically
multiplicative, asymptotically star-preserving, pointwise bounded, and
trace-correct in operator norm, then the group itself is operator MF with
separation constant `1`.

The mechanism, following `research/regular-character-mf-trace-implies-
group-mf-proof.md`: the trace clause at `1` pins a macroscopic unit
corner, obtained by spectral rounding of the hermitian part of the image
of `1`; inflating the cornered images by the corner complement produces
full near-unitaries, which polar-correct to exact unitaries; and the
trace clause at `g ≠ 1` makes the corrected unitaries separate at
Hilbert–Schmidt distance `√2`, which the operator norm dominates.

The two analytic bricks are already in the library: quantitative
involution rounding (`ApproxInvolutionCorner`) and quantitative polar
correction under a Gram-defect bound (`KazhdanCornerPolar`).

**Status: statement-complete; the quantitative assembly is in progress.**
This module is not yet imported by the library root.
-/

namespace GroupApproximation
namespace MFTraceRecognition

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable (G : Type u) [Group G]

/-- A finite-test-set matrix model of the regular character: operator-norm
multiplicativity, star-compatibility, and trace-correctness on the test
set, with a pointwise norm bound.  This is the local form of Shulman's
MF-trace condition for the canonical trace of the full group
`C^*`-algebra, restricted to the group unitaries. -/
structure RegularCharacterModel (F : Finset G) (ε : ℝ) (B : G → ℝ) where
  /-- The finite model space. -/
  carrier : FiniteModel
  /-- The model space is nonempty. -/
  nonempty : 0 < Fintype.card carrier
  /-- The matrix images of the group elements. -/
  map : G → Matrix carrier carrier ℂ
  /-- Pointwise norm bound, uniform over the accuracy parameter. -/
  bounded : ∀ g ∈ F, ‖map g‖ ≤ B g
  /-- Operator-norm multiplicativity on the test set. -/
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, ‖map (g * h) - map g * map h‖ ≤ ε
  /-- Star-compatibility on the test set. -/
  star_compatible : ∀ g ∈ F, ‖map g⁻¹ - (map g)ᴴ‖ ≤ ε
  /-- Trace-correctness at the identity. -/
  trace_correct_one : (1 : G) ∈ F →
    ‖(Matrix.trace (map 1)) / (Fintype.card carrier : ℂ) - 1‖ ≤ ε
  /-- Trace-correctness away from the identity. -/
  trace_correct_ne : ∀ g ∈ F, g ≠ 1 →
    ‖(Matrix.trace (map g)) / (Fintype.card carrier : ℂ)‖ ≤ ε

/-- The regular character of `G` is an MF trace: models exist at every
finite test set and accuracy, with a pointwise bound independent of the
accuracy. -/
def IsMFRegularCharacter : Prop :=
  ∃ B : G → ℝ, ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    Nonempty (RegularCharacterModel G F ε B)

/-! ## Unconditional spectral rounding

The library's involution rounding assumes a unitary source; the trace
argument rounds the hermitian part of the possibly non-unitary image of
`1`, so the scalar estimate is needed without the unit-interval
hypothesis. -/

theorem abs_signed_sub_le_abs_sq_sub_one' (lambda : ℝ) :
    |(if 0 < lambda then 1 else -1) - lambda| ≤ |lambda ^ 2 - 1| := by
  by_cases hpos : 0 < lambda
  · rw [if_pos hpos]
    have h1 : lambda ^ 2 - 1 = (lambda - 1) * (lambda + 1) := by ring
    rw [h1, abs_mul, abs_sub_comm 1 lambda]
    have h3 : (1 : ℝ) ≤ |lambda + 1| := by
      rw [abs_of_pos (by linarith)]
      linarith
    nlinarith [abs_nonneg (lambda - 1)]
  · have hneg : lambda ≤ 0 := not_lt.mp hpos
    rw [if_neg hpos]
    have h1 : lambda ^ 2 - 1 = (lambda - 1) * (lambda + 1) := by ring
    rw [h1, abs_mul,
      show |(-1 : ℝ) - lambda| = |lambda + 1| from by
        rw [show (-1 : ℝ) - lambda = -(lambda + 1) from by ring, abs_neg]]
    have h3 : (1 : ℝ) ≤ |lambda - 1| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    nlinarith [abs_nonneg (lambda + 1)]

open ApproxInvolutionCorner in
/-- **Unconditional matrix rounding**: for any square complex matrix, the
rounded symmetry is within the hermitian involution defect of the
hermitian part — no unitarity needed. -/
theorem norm_roundedInvolution_sub_hermitianPart_le'
    {Y : Type*} [Fintype Y] [DecidableEq Y] (U : Matrix Y Y ℂ) :
    ‖roundedInvolution U - hermitianPart U‖ ≤
      ‖hermitianPart U * hermitianPart U - 1‖ := by
  classical
  let H : Matrix Y Y ℂ := hermitianPart U
  let hH : H.IsHermitian := hermitianPart_isHermitian U
  let V : Matrix Y Y ℂ := hH.eigenvectorUnitary
  let P : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ if 0 < hH.eigenvalues i then 1 else 0)
  let L : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ))
  let R : Matrix Y Y ℂ :=
    Matrix.diagonal (fun i ↦
      (((if 0 < hH.eigenvalues i then 1 else -1) -
        hH.eigenvalues i : ℝ) : ℂ))
  have hVstarV : Vᴴ * V = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hVVstar : V * Vᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hHdiag : H = V * L * Vᴴ := by
    calc
      H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = V * L * Vᴴ := by rfl
  have hPdef : positiveProjection U = V * P * Vᴴ := by
    rfl
  have hcore : (2 : ℂ) • P - 1 - L = R := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hH.eigenvalues i
      · simp [P, L, R, hi]
        norm_num
      · simp [P, L, R, hi]
    · simp [P, L, R, hij]
  have hrewrite : roundedInvolution U - hermitianPart U = V * R * Vᴴ := by
    rw [roundedInvolution, hPdef]
    change (2 : ℂ) • (V * P * Vᴴ) - 1 - H = V * R * Vᴴ
    rw [hHdiag, show (1 : Matrix Y Y ℂ) = V * Vᴴ by exact hVVstar.symm]
    calc
      (2 : ℂ) • (V * P * Vᴴ) - V * Vᴴ - V * L * Vᴴ =
          V * ((2 : ℂ) • P - 1 - L) * Vᴴ := by
            have hsmul : (2 : ℂ) • (V * P * Vᴴ) =
                V * ((2 : ℂ) • P) * Vᴴ := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
            rw [hsmul]
            noncomm_ring
      _ = V * R * Vᴴ := by rw [hcore]
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hVstarV
  rw [hrewrite, CStarRing.norm_mul_mem_unitary _ hVstar,
    CStarRing.norm_mem_unitary_mul _ hH.eigenvectorUnitary.2]
  change ‖R‖ ≤ ‖H * H - 1‖
  change ‖Matrix.diagonal (fun i ↦
    (((if 0 < hH.eigenvalues i then 1 else -1) -
      hH.eigenvalues i : ℝ) : ℂ))‖ ≤ ‖H * H - 1‖
  rw [Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_signed_sub_le_abs_sq_sub_one' _).trans
    (abs_hermitianEigenvalue_sq_sub_one_le H hH i)

/-! ## The unit projection of a trace-correct model -/

section Rounding

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

open ApproxInvolutionCorner

/-- The rounded unit projection of an approximate idempotent. -/
noncomputable def unitProjection (M1 : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  positiveProjection ((2 : ℂ) • M1 - 1)

theorem unitProjection_isOrthogonalProjection (M1 : Matrix Y Y ℂ) :
    (unitProjection M1)ᴴ = unitProjection M1 ∧
      unitProjection M1 * unitProjection M1 = unitProjection M1 :=
  positiveProjection_isOrthogonalProjection _

omit [Fintype Y] in
theorem hermitianPart_two_smul_sub_one (M1 : Matrix Y Y ℂ) :
    hermitianPart ((2 : ℂ) • M1 - 1) =
      (2 : ℂ) • hermitianPart M1 - 1 := by
  unfold hermitianPart
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one]
  rw [show (star (2 : ℂ)) = (2 : ℂ) from by norm_num]
  module

theorem roundedInvolution_eq_two_smul_sub_one (M1 : Matrix Y Y ℂ) :
    roundedInvolution ((2 : ℂ) • M1 - 1) =
      (2 : ℂ) • unitProjection M1 - 1 := by
  rfl

/-- The rounded projection is within twice the hermitian idempotent
defect plus half the star defect of the model unit. -/
theorem norm_unitProjection_sub (M1 : Matrix Y Y ℂ) :
    ‖unitProjection M1 - M1‖ ≤
      2 * ‖hermitianPart M1 * hermitianPart M1 - hermitianPart M1‖ +
        ‖M1 - M1ᴴ‖ / 2 := by
  have hstep1 : ‖unitProjection M1 - hermitianPart M1‖ ≤
      2 * ‖hermitianPart M1 * hermitianPart M1 - hermitianPart M1‖ := by
    have hround := norm_roundedInvolution_sub_hermitianPart_le'
      ((2 : ℂ) • M1 - 1)
    rw [roundedInvolution_eq_two_smul_sub_one,
      hermitianPart_two_smul_sub_one] at hround
    have hlhs : (2 : ℂ) • unitProjection M1 - 1 -
        ((2 : ℂ) • hermitianPart M1 - 1) =
        (2 : ℂ) • (unitProjection M1 - hermitianPart M1) := by
      module
    have hrhs : ((2 : ℂ) • hermitianPart M1 - 1) *
        ((2 : ℂ) • hermitianPart M1 - 1) - 1 =
        (4 : ℂ) • (hermitianPart M1 * hermitianPart M1 -
          hermitianPart M1) := by
      have hcomm : ((2 : ℂ) • hermitianPart M1 - 1) *
          ((2 : ℂ) • hermitianPart M1 - 1) =
          (4 : ℂ) • (hermitianPart M1 * hermitianPart M1) -
            (4 : ℂ) • hermitianPart M1 + 1 := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
          Matrix.one_mul, smul_smul]
        norm_num
        module
      rw [hcomm]
      module
    rw [hlhs, hrhs] at hround
    rw [norm_smul, norm_smul] at hround
    simp only [Complex.norm_ofNat] at hround
    linarith [hround]
  have hstep2 : ‖hermitianPart M1 - M1‖ = ‖M1 - M1ᴴ‖ / 2 := by
    have h1 : hermitianPart M1 - M1 = ((2 : ℂ)⁻¹) • (M1ᴴ - M1) := by
      unfold hermitianPart
      module
    rw [h1, norm_smul]
    rw [show ‖((2 : ℂ)⁻¹)‖ = 2⁻¹ from by norm_num]
    rw [show (M1ᴴ - M1 : Matrix Y Y ℂ) = -(M1 - M1ᴴ) from by abel,
      norm_neg]
    ring
  calc ‖unitProjection M1 - M1‖
      = ‖(unitProjection M1 - hermitianPart M1) +
          (hermitianPart M1 - M1)‖ := by abel_nf
    _ ≤ ‖unitProjection M1 - hermitianPart M1‖ +
          ‖hermitianPart M1 - M1‖ := norm_add_le _ _
    _ ≤ 2 * ‖hermitianPart M1 * hermitianPart M1 - hermitianPart M1‖ +
          ‖M1 - M1ᴴ‖ / 2 := by
        rw [hstep2]
        linarith [hstep1]

end Rounding

/-! ## Corner inflation

The cornered model image, inflated by the complement of the unit
projection, is an exact algebraic near-unitary: its Gram defect equals
the corner Gram defect on the nose, and the latter is controlled by the
model defects. -/

section CornerInflation

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- An orthogonal projection is a contraction. -/
theorem norm_proj_le_one {p : Matrix Y Y ℂ}
    (hp : pᴴ = p) (hp2 : p * p = p) : ‖p‖ ≤ 1 := by
  rcases eq_or_ne p 0 with rfl | hne
  · simp
  · have hsq : ‖p‖ * ‖p‖ = ‖p‖ := by
      calc ‖p‖ * ‖p‖ = ‖pᴴ * p‖ := (Matrix.l2_opNorm_conjTranspose_mul_self p).symm
        _ = ‖p‖ := by rw [hp, hp2]
    have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hne
    nlinarith

/-- The inflated corner element. -/
noncomputable def inflate (p A : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  p * A * p + (1 - p)

/-- **Exact Gram identity for the inflation**: the Gram defect of the
inflated element is the corner Gram defect. -/
theorem inflate_gram (p A : Matrix Y Y ℂ)
    (hp : pᴴ = p) (hp2 : p * p = p) :
    (inflate p A)ᴴ * inflate p A - 1 =
      (p * A * p)ᴴ * (p * A * p) - p := by
  have hcorner_star : (p * A * p)ᴴ = p * Aᴴ * p := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hp]
    noncomm_ring
  have hleft : (p * Aᴴ * p) * (1 - p) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc (p * Aᴴ) p p,
      hp2, sub_self]
  have hright : (1 - p) * (p * A * p) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul,
      show p * (p * A * p) = (p * p) * (A * p) from by noncomm_ring,
      hp2, show p * (A * p) = p * A * p from by noncomm_ring, sub_self]
  have hcompl : (1 - p) * (1 - p) = 1 - p := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hp2]
    abel
  rw [inflate, Matrix.conjTranspose_add, hcorner_star,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hp]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [hleft, hright, hcompl]
  abel

/-- The corner Gram defect from the model defects.  `B₁` plays the role
of the model image of the identity. -/
theorem corner_gram_bound {p A B₁ : Matrix Y Y ℂ} {C η δ₁ δ₂ : ℝ}
    (hp : pᴴ = p) (hp2 : p * p = p)
    (hA : ‖A‖ ≤ C) (hC : 0 ≤ C)
    (hη : ‖p - B₁‖ ≤ η)
    (hδ₁ : ‖B₁ * A - A‖ ≤ δ₁)
    (hδ₂ : ‖Aᴴ * A - B₁‖ ≤ δ₂) :
    ‖(p * A * p)ᴴ * (p * A * p) - p‖ ≤
      C * (C * η + δ₁) + δ₂ + η := by
  have hpn : ‖p‖ ≤ 1 := norm_proj_le_one hp hp2
  have hAstar : ‖Aᴴ‖ = ‖A‖ := Matrix.l2_opNorm_conjTranspose A
  have hcorner_star : (p * A * p)ᴴ = p * Aᴴ * p := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hp]
    noncomm_ring
  have hsplit : (p * A * p)ᴴ * (p * A * p) - p =
      (p * Aᴴ) * ((p - 1) * (A * p)) +
        ((p * (Aᴴ * A - B₁) * p) + (p * (B₁ - p) * p)) := by
    rw [hcorner_star]
    have hp3 : p * p * p = p := by rw [hp2, hp2]
    calc p * Aᴴ * p * (p * A * p) - p
        = p * Aᴴ * ((p * p) * (A * p)) - p := by noncomm_ring
      _ = p * Aᴴ * (p * (A * p)) - p := by rw [hp2]
      _ = p * Aᴴ * ((p - 1) * (A * p)) + p * (Aᴴ * A) * p - p := by
          noncomm_ring
      _ = p * Aᴴ * ((p - 1) * (A * p)) +
            (p * (Aᴴ * A - B₁) * p + p * (B₁ - p) * p) +
            (p * p * p - p) := by noncomm_ring
      _ = _ := by rw [hp3]; abel
  rw [hsplit]
  have h1 : ‖(p * Aᴴ) * ((p - 1) * (A * p))‖ ≤ C * (C * η + δ₁) := by
    have hin : ‖(p - 1) * (A * p)‖ ≤ C * η + δ₁ := by
      have hcalc : (p - 1) * (A * p) = ((p - B₁) * A) * p +
          ((B₁ * A - A) * p) := by noncomm_ring
      rw [hcalc]
      calc ‖((p - B₁) * A) * p + (B₁ * A - A) * p‖
          ≤ ‖((p - B₁) * A) * p‖ + ‖(B₁ * A - A) * p‖ := norm_add_le _ _
        _ ≤ ‖(p - B₁) * A‖ * ‖p‖ + ‖B₁ * A - A‖ * ‖p‖ := by
            gcongr <;> exact Matrix.l2_opNorm_mul _ _
        _ ≤ ‖p - B₁‖ * ‖A‖ * 1 + δ₁ * 1 := by
            have := Matrix.l2_opNorm_mul (p - B₁) A
            have hδ₁0 : (0 : ℝ) ≤ δ₁ := (norm_nonneg _).trans hδ₁
            gcongr
        _ ≤ η * C + δ₁ := by
            have hmul : ‖p - B₁‖ * ‖A‖ ≤ η * C :=
              mul_le_mul hη hA (norm_nonneg A)
                ((norm_nonneg (p - B₁)).trans hη)
            linarith
        _ = C * η + δ₁ := by ring
    calc ‖(p * Aᴴ) * ((p - 1) * (A * p))‖
        ≤ ‖p * Aᴴ‖ * ‖(p - 1) * (A * p)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * C) * (C * η + δ₁) := by
          have hpa : ‖p * Aᴴ‖ ≤ 1 * C := by
            calc ‖p * Aᴴ‖ ≤ ‖p‖ * ‖Aᴴ‖ := Matrix.l2_opNorm_mul _ _
              _ ≤ 1 * C := by rw [hAstar]; gcongr
          have hnn : (0 : ℝ) ≤ C * η + δ₁ := by
            have := (norm_nonneg ((p - 1) * (A * p))).trans hin
            linarith [norm_nonneg ((p - 1) * (A * p))]
          gcongr
      _ = C * (C * η + δ₁) := by ring
  have h2 : ‖p * (Aᴴ * A - B₁) * p‖ ≤ δ₂ := by
    calc ‖p * (Aᴴ * A - B₁) * p‖
        ≤ ‖p * (Aᴴ * A - B₁)‖ * ‖p‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖p‖ * ‖Aᴴ * A - B₁‖) * ‖p‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * δ₂) * 1 := by
          have hmul : ‖p‖ * ‖Aᴴ * A - B₁‖ ≤ 1 * δ₂ :=
            mul_le_mul hpn hδ₂ (norm_nonneg _) zero_le_one
          have := mul_le_mul hmul hpn (norm_nonneg p)
            (by linarith [(norm_nonneg (Aᴴ * A - B₁)).trans hδ₂] :
              (0 : ℝ) ≤ 1 * δ₂)
          linarith
      _ = δ₂ := by ring
  have h3 : ‖p * (B₁ - p) * p‖ ≤ η := by
    calc ‖p * (B₁ - p) * p‖
        ≤ ‖p * (B₁ - p)‖ * ‖p‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖p‖ * ‖B₁ - p‖) * ‖p‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * η) * 1 := by
          have hswap : ‖B₁ - p‖ ≤ η := by
            rw [show B₁ - p = -(p - B₁) from by abel, norm_neg]
            exact hη
          have hmul : ‖p‖ * ‖B₁ - p‖ ≤ 1 * η :=
            mul_le_mul hpn hswap (norm_nonneg _) zero_le_one
          have := mul_le_mul hmul hpn (norm_nonneg p)
            (by linarith [(norm_nonneg (p - B₁)).trans hη] :
              (0 : ℝ) ≤ 1 * η)
          linarith
      _ = η := by ring
  calc ‖(p * Aᴴ) * ((p - 1) * (A * p)) +
      ((p * (Aᴴ * A - B₁) * p) + (p * (B₁ - p) * p))‖
      ≤ ‖(p * Aᴴ) * ((p - 1) * (A * p))‖ +
          (‖p * (Aᴴ * A - B₁) * p‖ + ‖p * (B₁ - p) * p‖) := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ C * (C * η + δ₁) + (δ₂ + η) := by
        gcongr
    _ = C * (C * η + δ₁) + δ₂ + η := by ring

open KazhdanCornerMatrices in
/-- **Exact unitary near the inflation.**  When the corner Gram defect is
at most `1/2`, polar correction turns the inflated corner into an exact
unitary at distance at most four times the defect. -/
theorem exists_unitary_near_inflate (p A : Matrix Y Y ℂ) {δ : ℝ}
    (hp : pᴴ = p) (hp2 : p * p = p) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hδ : ‖(p * A * p)ᴴ * (p * A * p) - p‖ ≤ δ) :
    ∃ U ∈ Matrix.unitaryGroup Y ℂ, ‖U - inflate p A‖ ≤ 4 * δ := by
  have hP : (cornerGram (inflate p A)).IsHermitian :=
    cornerGram_isHermitian _
  have hgram : ‖cornerGram (inflate p A) - 1‖ ≤ δ := by
    rw [cornerGram, inflate_gram p A hp hp2]
    exact hδ
  refine ⟨polarCorrect (inflate p A) hP,
    polarCorrect_mem_unitaryGroup _ hP
      (cornerGram_eigenvalues_pos_of_norm_sub_one_le _ hP hδhalf hgram),
    ?_⟩
  have hCsq : ‖inflate p A‖ * ‖inflate p A‖ ≤ (3 : ℝ) / 2 := by
    have hgs : (inflate p A)ᴴ * inflate p A =
        (cornerGram (inflate p A) - 1) + 1 := by
      rw [cornerGram]; abel
    have hone : ‖(1 : Matrix Y Y ℂ)‖ ≤ 1 :=
      norm_proj_le_one Matrix.conjTranspose_one (one_mul 1)
    calc ‖inflate p A‖ * ‖inflate p A‖
        = ‖(inflate p A)ᴴ * inflate p A‖ :=
          (Matrix.l2_opNorm_conjTranspose_mul_self _).symm
      _ = ‖(cornerGram (inflate p A) - 1) + 1‖ := by rw [← hgs]
      _ ≤ ‖cornerGram (inflate p A) - 1‖ + ‖(1 : Matrix Y Y ℂ)‖ :=
          norm_add_le _ _
      _ ≤ δ + 1 := by gcongr
      _ ≤ 3 / 2 := by linarith
  have hCn : ‖inflate p A‖ ≤ 2 := by nlinarith [norm_nonneg (inflate p A)]
  calc ‖polarCorrect (inflate p A) hP - inflate p A‖
      ≤ ‖inflate p A‖ * (2 * δ) :=
        norm_polarCorrect_sub_le_mul _ hP hδ0 hδhalf hgram
    _ ≤ 2 * (2 * δ) := by
        have h2δ : (0 : ℝ) ≤ 2 * δ := by linarith
        exact mul_le_mul_of_nonneg_right hCn h2δ
    _ = 4 * δ := by ring

end CornerInflation

/-! ## Trace separation

The normalized trace is dominated by the operator norm, so trace-small
unitaries are operator-norm antipodal: the Hilbert–Schmidt identity puts
their squared distance near `2`, and the operator norm dominates the
normalized Hilbert–Schmidt distance. -/

section TraceSeparation

/-- The normalized trace is dominated by the operator norm. -/
theorem norm_normTrace_le (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (M : Matrix Y Y ℂ) : ‖normTrace Y M‖ ≤ ‖M‖ := by
  have hentry : ∀ i : Y, ‖M i i‖ ≤ ‖M‖ := by
    intro i
    have h := normSq_entry_le_sq_l2_opNorm Y M i i
    have h2 : ‖M i i‖ ^ 2 ≤ ‖M‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact h
    nlinarith [norm_nonneg (M i i), norm_nonneg M]
  have htr : ‖Matrix.trace M‖ ≤ (Fintype.card Y : ℝ) * ‖M‖ := by
    calc ‖Matrix.trace M‖ = ‖∑ i : Y, M i i‖ := rfl
      _ ≤ ∑ i : Y, ‖M i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Y, ‖M‖ := Finset.sum_le_sum fun i _ ↦ hentry i
      _ = (Fintype.card Y : ℝ) * ‖M‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  rw [normTrace, norm_div, Complex.norm_natCast, div_le_iff₀ hc]
  exact htr.trans_eq (mul_comm _ _)

/-- **Antipodal separation from a small normalized trace.**  Two
unitaries whose relative normalized trace has modulus at most `1/2` are
at operator distance at least `1`. -/
theorem one_le_norm_sub_of_normTrace_small (Y : FiniteModel)
    {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y)
    (htr : ‖normTrace Y (A * Bᴴ)‖ ≤ 1 / 2) :
    1 ≤ ‖A - B‖ := by
  have habs : |(normTrace Y (A * Bᴴ)).re| ≤ 1 / 2 :=
    le_trans (Complex.abs_re_le_norm _) htr
  have hd1 : (1 : ℝ) ≤ hsDistSq Y A B := by
    rw [hsDistSq_of_unitary Y hA hB hY]
    have := (abs_le.mp habs).2
    linarith
  have hop := hsDistSq_le_sq_l2_opNorm Y A B
  nlinarith [norm_nonneg (A - B)]

/-- **Projection-trace domination**: against an orthogonal projection,
the trace pairing is bounded by the operator norm times the dimension of
the projection, not the dimension of the space. -/
theorem norm_trace_mul_proj_le (Y : FiniteModel)
    {q : Matrix Y Y ℂ} (hq : qᴴ = q) (hq2 : q * q = q)
    (X : Matrix Y Y ℂ) :
    ‖Matrix.trace (X * q)‖ ≤ ‖X‖ * (Matrix.trace q).re := by
  classical
  have hcycle : Matrix.trace (q * X * q) = Matrix.trace (X * q) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hq2]
  set s : Y → ℝ := fun i => ∑ j : Y, Complex.normSq (q j i) with hs
  have hs_nonneg : ∀ i, 0 ≤ s i := fun i =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hsum_s : ∑ i : Y, s i = (Matrix.trace q).re := by
    have hqq : qᴴ * q = q := by rw [hq, hq2]
    have hdiag : ∀ i : Y, s i = ((qᴴ * q) i i).re := by
      intro i
      rw [Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply]
      simp [Complex.mul_re, Complex.normSq_apply]
    calc ∑ i : Y, s i = ∑ i : Y, ((qᴴ * q) i i).re :=
          Finset.sum_congr rfl fun i _ => hdiag i
      _ = (Matrix.trace (qᴴ * q)).re := by
          rw [Matrix.trace, ← Complex.re_sum]
          rfl
      _ = (Matrix.trace q).re := by rw [hqq]
  have hentry : ∀ i : Y, ‖(q * X * q) i i‖ ≤ ‖X‖ * s i := by
    intro i
    set v : Y → ℂ := fun j => q j i with hv
    have hform : (q * X * q) i i =
        ∑ j : Y, (starRingEnd ℂ) (v j) * (X.mulVec v) j := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hqij : q i j = (starRingEnd ℂ) (q j i) := by
        conv_lhs => rw [← hq]
        rfl
      rw [hqij]
      congr 1
    have hb := sum_normSq_mulVec_le Y X v
    have hva : ∑ j : Y, Complex.normSq (v j) = s i := rfl
    have hS : ∑ j : Y, ‖v j‖ * ‖(X.mulVec v) j‖ ≤ ‖X‖ * s i := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ)
        Finset.univ (fun j => ‖v j‖) (fun j => ‖(X.mulVec v) j‖)
      have hsq : (∑ j : Y, ‖v j‖ * ‖(X.mulVec v) j‖) ^ 2 ≤
          (∑ j : Y, Complex.normSq (v j)) *
            (∑ j : Y, Complex.normSq ((X.mulVec v) j)) := by
        have h1 : ∀ j : Y, Complex.normSq (v j) = ‖v j‖ ^ 2 := fun j =>
          Complex.normSq_eq_norm_sq _
        have h2 : ∀ j : Y, Complex.normSq ((X.mulVec v) j) =
            ‖(X.mulVec v) j‖ ^ 2 := fun j => Complex.normSq_eq_norm_sq _
        simp only [h1, h2]
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      have hXv : ∑ j : Y, Complex.normSq ((X.mulVec v) j) ≤
          ‖X‖ ^ 2 * s i := by rw [← hva]; exact hb
      have hprod : (∑ j : Y, ‖v j‖ * ‖(X.mulVec v) j‖) ^ 2 ≤
          (‖X‖ * s i) ^ 2 := by
        calc (∑ j : Y, ‖v j‖ * ‖(X.mulVec v) j‖) ^ 2
            ≤ (∑ j : Y, Complex.normSq (v j)) *
              (∑ j : Y, Complex.normSq ((X.mulVec v) j)) := hsq
          _ ≤ s i * (‖X‖ ^ 2 * s i) := by
              rw [hva]
              exact mul_le_mul_of_nonneg_left hXv (hs_nonneg i)
          _ = (‖X‖ * s i) ^ 2 := by ring
      have hnn : (0 : ℝ) ≤ ∑ j : Y, ‖v j‖ * ‖(X.mulVec v) j‖ :=
        Finset.sum_nonneg fun j _ =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith [mul_nonneg (norm_nonneg X) (hs_nonneg i)]
    calc ‖(q * X * q) i i‖
        = ‖∑ j : Y, (starRingEnd ℂ) (v j) * (X.mulVec v) j‖ := by
          rw [hform]
      _ ≤ ∑ j : Y, ‖(starRingEnd ℂ) (v j) * (X.mulVec v) j‖ :=
          norm_sum_le _ _
      _ = ∑ j : Y, ‖v j‖ * ‖(X.mulVec v) j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, RCLike.norm_conj]
      _ ≤ ‖X‖ * s i := hS
  calc ‖Matrix.trace (X * q)‖ = ‖Matrix.trace (q * X * q)‖ := by
        rw [hcycle]
    _ = ‖∑ i : Y, (q * X * q) i i‖ := rfl
    _ ≤ ∑ i : Y, ‖(q * X * q) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Y, ‖X‖ * s i := Finset.sum_le_sum fun i _ => hentry i
    _ = ‖X‖ * (Matrix.trace q).re := by
        rw [← Finset.mul_sum, hsum_s]

/-- **Corner trace correction**: inflating a corner changes the
normalized trace by at most the codimension weight of the corner. -/
theorem norm_normTrace_inflate_sub (Y : FiniteModel)
    {p : Matrix Y Y ℂ} (hp : pᴴ = p) (hp2 : p * p = p)
    (X : Matrix Y Y ℂ) :
    ‖normTrace Y (p * X * p + (1 - p)) - normTrace Y X‖ ≤
      (1 + 3 * ‖X‖) * (Matrix.trace (1 - p)).re / Fintype.card Y := by
  classical
  set q : Matrix Y Y ℂ := 1 - p with hqdef
  have hqherm : qᴴ = q := by
    rw [hqdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hp]
  have hqidem : q * q = q := by
    rw [hqdef, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hp2]
    abel
  have hqtr_nonneg : 0 ≤ (Matrix.trace q).re := by
    have h := norm_trace_mul_proj_le Y hqherm hqidem 1
    rw [Matrix.one_mul] at h
    by_contra hneg
    push Not at hneg
    have habs : |(Matrix.trace q).re| ≤ ‖Matrix.trace q‖ :=
      Complex.abs_re_le_norm _
    rw [abs_of_neg hneg] at habs
    -- a nonnegative multiple of a negative number is nonpositive, so the
    -- norm is squeezed to zero and the real part cannot be negative
    nlinarith [norm_nonneg (1 : Matrix Y Y ℂ), norm_nonneg (Matrix.trace q)]
  have hdecomp : p * X * p + q - X = q - (q * X + X * q - q * X * q) := by
    have hpq : p = 1 - q := by rw [hqdef]; abel
    rw [hpq]
    noncomm_ring
  have htr_qX : ‖Matrix.trace (q * X)‖ ≤ ‖X‖ * (Matrix.trace q).re := by
    rw [Matrix.trace_mul_comm]
    exact norm_trace_mul_proj_le Y hqherm hqidem X
  have htr_Xq : ‖Matrix.trace (X * q)‖ ≤ ‖X‖ * (Matrix.trace q).re :=
    norm_trace_mul_proj_le Y hqherm hqidem X
  have htr_qXq : ‖Matrix.trace (q * X * q)‖ ≤
      ‖X‖ * (Matrix.trace q).re := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hqidem]
    exact htr_Xq
  have hnum : ‖Matrix.trace (p * X * p + q) - Matrix.trace X‖ ≤
      (1 + 3 * ‖X‖) * (Matrix.trace q).re := by
    have h1 : Matrix.trace (p * X * p + q) - Matrix.trace X =
        Matrix.trace q - (Matrix.trace (q * X) + Matrix.trace (X * q) -
          Matrix.trace (q * X * q)) := by
      rw [← Matrix.trace_sub, ← Matrix.trace_add, ← Matrix.trace_sub,
        ← Matrix.trace_sub]
      congr 1
    rw [h1]
    have htrq : ‖Matrix.trace q‖ ≤ (Matrix.trace q).re := by
      have h := norm_trace_mul_proj_le Y hqherm hqidem 1
      rw [Matrix.one_mul] at h
      have hXn : ‖(1 : Matrix Y Y ℂ)‖ ≤ 1 :=
        norm_proj_le_one Matrix.conjTranspose_one (one_mul 1)
      exact h.trans (by nlinarith)
    calc ‖Matrix.trace q - (Matrix.trace (q * X) + Matrix.trace (X * q) -
        Matrix.trace (q * X * q))‖
        ≤ ‖Matrix.trace q‖ + ‖Matrix.trace (q * X) + Matrix.trace (X * q) -
            Matrix.trace (q * X * q)‖ := norm_sub_le _ _
      _ ≤ ‖Matrix.trace q‖ + (‖Matrix.trace (q * X)‖ +
            ‖Matrix.trace (X * q)‖ + ‖Matrix.trace (q * X * q)‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (Matrix.trace q).re + (‖X‖ * (Matrix.trace q).re +
            ‖X‖ * (Matrix.trace q).re + ‖X‖ * (Matrix.trace q).re) := by
          gcongr
      _ = (1 + 3 * ‖X‖) * (Matrix.trace q).re := by ring
  have hcard : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hzero | hpos
  · rw [normTrace, normTrace, hzero]
    push_cast
    simp
  · have hcpos : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hpos
    rw [normTrace, normTrace, div_sub_div_same, ← Matrix.trace_sub]
    rw [norm_div, Complex.norm_natCast, div_le_div_iff_of_pos_right hcpos]
    rw [Matrix.trace_sub]
    exact hnum

end TraceSeparation

/-! ## Assembly helpers

The inflation is a monoid map through the corner and commutes with the
adjoint; both are exact algebraic identities, and they are what turn the
corner estimates into statements about the corrected unitaries. -/

section Assembly

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **Inflation is multiplicative through the corner**: the product of two
inflations is the inflation of the corner-mediated product. -/
theorem inflate_mul (p A B : Matrix Y Y ℂ) (hp2 : p * p = p) :
    inflate p A * inflate p B = inflate p (A * p * B) := by
  unfold inflate
  have e1 : p * A * p * (p * B * p) = p * (A * p * B) * p := by
    calc p * A * p * (p * B * p) = p * A * (p * p) * (B * p) := by
          noncomm_ring
      _ = p * A * p * (B * p) := by rw [hp2]
      _ = p * (A * p * B) * p := by noncomm_ring
  have e2 : p * A * p * (1 - p) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc (p * A) p p, hp2,
      sub_self]
  have e3 : (1 - p) * (p * B * p) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul,
      show p * (p * B * p) = (p * p) * (B * p) from by noncomm_ring, hp2,
      show p * (B * p) = p * B * p from by noncomm_ring, sub_self]
  have e4 : (1 - p) * (1 - p) = 1 - p := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hp2]
    abel
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4]
  abel

/-- **Inflation commutes with the adjoint.** -/
theorem inflate_conjTranspose (p A : Matrix Y Y ℂ) (hp : pᴴ = p) :
    (inflate p A)ᴴ = inflate p Aᴴ := by
  unfold inflate
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hp, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hp]
  noncomm_ring

/-- The inflation of a bounded element is bounded by that bound plus one. -/
theorem norm_inflate_le {p A : Matrix Y Y ℂ} {C : ℝ}
    (hp : pᴴ = p) (hp2 : p * p = p) (hA : ‖A‖ ≤ C) (hC : 0 ≤ C) :
    ‖inflate p A‖ ≤ C + 1 := by
  have hpn : ‖p‖ ≤ 1 := norm_proj_le_one hp hp2
  have hcompl : ‖(1 : Matrix Y Y ℂ) - p‖ ≤ 1 := by
    refine norm_proj_le_one ?_ ?_
    · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hp]
    · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hp2]
      abel
  refine (norm_add_le _ _).trans ?_
  gcongr
  calc ‖p * A * p‖ ≤ ‖p * A‖ * ‖p‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖p‖ * ‖A‖) * ‖p‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * C) * 1 := by
        refine mul_le_mul (mul_le_mul hpn hA (norm_nonneg _) zero_le_one)
          hpn (norm_nonneg _) (by linarith)
    _ = C := by ring

end Assembly

/-- The normalized trace is additive on differences. -/
theorem normTrace_sub' (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    normTrace Y (A - B) = normTrace Y A - normTrace Y B := by
  unfold normTrace
  rw [Matrix.trace_sub, sub_div]

/-- **The codimension weight of the unit corner is small.**  If the model
unit has normalized trace within `e` of one, and the rounded projection is
within `η` of that unit, then the corner complement carries relative
dimension at most `e + η`.

This is the estimate the separation clause turns on.  The trivial bound
`‖1 - p‖ ≤ 1` is available but useless here: the corner correction in
`norm_normTrace_inflate_sub` is weighted by exactly this quantity, and a
bound of `1` would leave the corrected trace unconstrained. -/
theorem codimension_weight_le (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    {M1 p : Matrix Y Y ℂ} {e η : ℝ}
    (htr : ‖normTrace Y M1 - 1‖ ≤ e) (hη : ‖p - M1‖ ≤ η) :
    (Matrix.trace ((1 : Matrix Y Y ℂ) - p)).re / (Fintype.card Y : ℝ)
      ≤ e + η := by
  have hc : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hone : normTrace Y (1 : Matrix Y Y ℂ) = 1 := by
    unfold normTrace
    rw [Matrix.trace_one]
    have hcne : ((Fintype.card Y : ℂ)) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
    field_simp
  have hbound : ‖normTrace Y ((1 : Matrix Y Y ℂ) - p)‖ ≤ e + η := by
    rw [normTrace_sub', hone]
    have h1 : (1 : ℂ) - normTrace Y p
        = -(normTrace Y M1 - 1) + normTrace Y (M1 - p) := by
      rw [normTrace_sub']
      ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    have hA : ‖-(normTrace Y M1 - 1)‖ ≤ e := by rwa [norm_neg]
    have hB : ‖normTrace Y (M1 - p)‖ ≤ η := by
      refine (norm_normTrace_le Y hY _).trans ?_
      rw [show M1 - p = -(p - M1) from by abel, norm_neg]
      exact hη
    linarith
  have hre : (Matrix.trace ((1 : Matrix Y Y ℂ) - p)).re
      ≤ ‖Matrix.trace ((1 : Matrix Y Y ℂ) - p)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hnormtr : ‖normTrace Y ((1 : Matrix Y Y ℂ) - p)‖
      = ‖Matrix.trace ((1 : Matrix Y Y ℂ) - p)‖ / (Fintype.card Y : ℝ) := by
    unfold normTrace
    rw [norm_div, Complex.norm_natCast]
  rw [hnormtr, div_le_iff₀ hc] at hbound
  rw [div_le_iff₀ hc]
  linarith

/-- **MF-trace recognition.**  If the regular character of a group is an
MF trace, the group is operator MF: the corner-and-polar correction of
any trace-correct model family produces operator-norm local models with
separation constant `1`.

The trace clause does all the work the weak definition cannot: at `1` it
pins the unit corner at relative dimension one, and at `g ≠ 1` it gives
separation `√2 - o(1) > 1` automatically. -/
theorem isNormApproximable_of_isMFRegularCharacter
    (h : IsMFRegularCharacter G) : IsNormApproximable G 1 := by
  sorry

end MFTraceRecognition
end GroupApproximation
