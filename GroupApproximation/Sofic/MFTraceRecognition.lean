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
  have hsum := positiveProjection_add_negativeProjection
    ((2 : ℂ) • M1 - 1)
  rw [roundedInvolution, unitProjection]
  try rw [show negativeProjection ((2 : ℂ) • M1 - 1) =
      1 - positiveProjection ((2 : ℂ) • M1 - 1) from by
    rw [← hsum]; try abel]
  try module

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
            gcongr <;> assumption
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

end CornerInflation

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
