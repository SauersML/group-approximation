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

The quantitative schedule: on a test set closed under inverses, products
and `g h⁻¹`, take the accuracy `e` below both `ε/(400 C⁴)` and
`1/(1000 C⁴)`, where `C` bounds the model images.  Then the rounded
projection sits within `9 e C` of the model unit, the corner Gram defect
is at most `21 e C³` — under `1/2`, so polar correction fires — and both
clauses come out at `400 e C⁴`, which is `≤ ε` for multiplicativity and
`≤ 1/2` for separation, with a factor of two to spare on the latter.
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

@[simp] theorem roundedInvolution_eq_two_smul_sub_one (M1 : Matrix Y Y ℂ) :
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

/-- Inflations of nearby elements are nearby: the difference is the
corner of the difference, and the corner is a contraction. -/
theorem norm_inflate_sub_inflate (p Z W : Matrix Y Y ℂ)
    (hp : pᴴ = p) (hp2 : p * p = p) :
    ‖inflate p Z - inflate p W‖ ≤ ‖Z - W‖ := by
  have hpn : ‖p‖ ≤ 1 := norm_proj_le_one hp hp2
  have hdiff : inflate p Z - inflate p W = p * (Z - W) * p := by
    unfold inflate
    noncomm_ring
  rw [hdiff]
  calc ‖p * (Z - W) * p‖ ≤ ‖p * (Z - W)‖ * ‖p‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖p‖ * ‖Z - W‖) * ‖p‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖Z - W‖) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hpn (norm_nonneg _)) hpn
          (norm_nonneg _) (by positivity)
    _ = ‖Z - W‖ := by ring

/-- **The rounded unit projection is close to the model unit.**  The
star defect and the idempotent defect of the model unit together pin the
rounded projection at distance `9 e C`. -/
theorem norm_unitProjection_sub_le {M1 : Matrix Y Y ℂ} {e C : ℝ}
    (hstar : ‖M1 - M1ᴴ‖ ≤ e) (hidem : ‖M1 * M1 - M1‖ ≤ e)
    (hnorm : ‖M1‖ ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hC : 1 ≤ C) :
    ‖unitProjection M1 - M1‖ ≤ 9 * e * C := by
  set H := ApproxInvolutionCorner.hermitianPart M1 with hHdef
  have hHM : ‖H - M1‖ ≤ e / 2 := by
    have h1 : H - M1 = ((2 : ℂ)⁻¹) • (M1ᴴ - M1) := by
      rw [hHdef]
      unfold ApproxInvolutionCorner.hermitianPart
      module
    rw [h1, norm_smul, show ‖((2 : ℂ)⁻¹)‖ = 2⁻¹ from by norm_num,
      show (M1ᴴ - M1 : Matrix Y Y ℂ) = -(M1 - M1ᴴ) from by abel, norm_neg]
    linarith
  have hHn : ‖H‖ ≤ C + e / 2 := by
    calc ‖H‖ = ‖(H - M1) + M1‖ := by congr 1; abel
      _ ≤ ‖H - M1‖ + ‖M1‖ := norm_add_le _ _
      _ ≤ C + e / 2 := by linarith
  have h1 : ‖H * (H - M1)‖ ≤ (C + e / 2) * (e / 2) :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hHn hHM (norm_nonneg _) (by linarith))
  have h2 : ‖(H - M1) * M1‖ ≤ (e / 2) * C :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hHM hnorm (norm_nonneg _) (by linarith))
  have h3 : ‖M1 - H‖ ≤ e / 2 := by
    rw [show M1 - H = -(H - M1) from by abel, norm_neg]
    exact hHM
  have hHH : ‖H * H - H‖ ≤ 4 * e * C := by
    have hsplit : H * H - H
        = (H * (H - M1) + (H - M1) * M1) + (M1 * M1 - M1) + (M1 - H) := by
      noncomm_ring
    rw [hsplit]
    calc ‖(H * (H - M1) + (H - M1) * M1) + (M1 * M1 - M1) + (M1 - H)‖
        ≤ ‖(H * (H - M1) + (H - M1) * M1) + (M1 * M1 - M1)‖ + ‖M1 - H‖ :=
          norm_add_le _ _
      _ ≤ (‖H * (H - M1) + (H - M1) * M1‖ + ‖M1 * M1 - M1‖) + ‖M1 - H‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((‖H * (H - M1)‖ + ‖(H - M1) * M1‖) + ‖M1 * M1 - M1‖)
            + ‖M1 - H‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (((C + e / 2) * (e / 2) + (e / 2) * C) + e) + e / 2 := by gcongr
      _ ≤ 4 * e * C := by nlinarith
  calc ‖unitProjection M1 - M1‖
      ≤ 2 * ‖H * H - H‖ + ‖M1 - M1ᴴ‖ / 2 := norm_unitProjection_sub M1
    _ ≤ 2 * (4 * e * C) + e / 2 := by gcongr
    _ ≤ 9 * e * C := by nlinarith

/-- A unitary matrix is an operator-norm contraction. -/
theorem norm_unitary_le_one {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) : ‖U‖ ≤ 1 := by
  have h1 : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hsq : ‖U‖ * ‖U‖ = ‖(1 : Matrix Y Y ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, h1]
  have hone : ‖(1 : Matrix Y Y ℂ)‖ ≤ 1 :=
    norm_proj_le_one Matrix.conjTranspose_one (one_mul 1)
  nlinarith [norm_nonneg U]

/-- **The corner Gram defect of a model image**, assembled from the
model's own multiplicativity, star-compatibility and norm bound. -/
theorem corner_defect_le {p M1 A Ainv : Matrix Y Y ℂ} {e C : ℝ}
    (hp : pᴴ = p) (hp2 : p * p = p)
    (hA : ‖A‖ ≤ C) (hC : 1 ≤ C) (he0 : 0 ≤ e)
    (hη : ‖p - M1‖ ≤ 9 * e * C)
    (hδ₁ : ‖M1 * A - A‖ ≤ e)
    (hstarA : ‖Ainv - Aᴴ‖ ≤ e)
    (hmulA : ‖M1 - Ainv * A‖ ≤ e) :
    ‖(p * A * p)ᴴ * (p * A * p) - p‖ ≤ 21 * e * C ^ 3 := by
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hδ₂ : ‖Aᴴ * A - M1‖ ≤ e * C + e := by
    have hsplit : Aᴴ * A - M1 = (Aᴴ - Ainv) * A + (Ainv * A - M1) := by
      noncomm_ring
    rw [hsplit]
    have h1 : ‖(Aᴴ - Ainv) * A‖ ≤ e * C := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul ?_ hA (norm_nonneg _) (by linarith)
      rw [show Aᴴ - Ainv = -(Ainv - Aᴴ) from by abel, norm_neg]
      exact hstarA
    have h2 : ‖Ainv * A - M1‖ ≤ e := by
      rw [show Ainv * A - M1 = -(M1 - Ainv * A) from by abel, norm_neg]
      exact hmulA
    exact (norm_add_le _ _).trans (by linarith)
  have hmain := corner_gram_bound (p := p) (A := A) (B₁ := M1)
    (C := C) (η := 9 * e * C) (δ₁ := e) (δ₂ := e * C + e)
    hp hp2 hA hC0 hη hδ₁ hδ₂
  refine hmain.trans ?_
  nlinarith [sq_nonneg C, sq_nonneg (C - 1), mul_nonneg he0 hC0]

end Assembly

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
    rw [normTrace_sub, hone]
    have h1 : (1 : ℂ) - normTrace Y p
        = -(normTrace Y M1 - 1) + normTrace Y (M1 - p) := by
      rw [normTrace_sub]
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

/-! ## The two clause estimates

Both are stated as free-standing lemmas over abstract matrices rather
than inlined into the recognition proof.  That is not stylistic: the
heartbeat budget is per declaration, and the assembled recognition
theorem exceeds it when either estimate is carried inside it. -/

section Estimates

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **The multiplicativity estimate.**  Corrected unitaries multiply to
within `400 e C⁴`: the corner mediates the product exactly, and the model
unit is a near-identity for the corner. -/
theorem mult_estimate {p M1 A Bm Agy Ug Uy Ugy : Matrix Y Y ℂ} {e C : ℝ}
    (hp : pᴴ = p) (hp2 : p * p = p) (hC1 : 1 ≤ C) (he0 : 0 ≤ e)
    (hnA : ‖A‖ ≤ C) (hnB : ‖Bm‖ ≤ C)
    (hη : ‖p - M1‖ ≤ 9 * e * C)
    (hmulAB : ‖Agy - A * Bm‖ ≤ e)
    (hδB : ‖M1 * Bm - Bm‖ ≤ e)
    (hUg : ‖Ug - inflate p A‖ ≤ 4 * (21 * e * C ^ 3))
    (hUy : ‖Uy - inflate p Bm‖ ≤ 4 * (21 * e * C ^ 3))
    (hUgy : ‖Ugy - inflate p Agy‖ ≤ 4 * (21 * e * C ^ 3))
    (hUyn : ‖Uy‖ ≤ 1) :
    ‖Ugy - Ug * Uy‖ ≤ 400 * e * C ^ 4 := by
  have hC0 : (0 : ℝ) < C := by linarith
  have hC3 : C ^ 3 ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hCC : C ≤ C ^ 4 := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hCone : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC1
  have hCe3 : e * C ^ 3 ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hC3 he0
  have hCe2 : e * C ^ 2 ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hC2 he0
  have hCeC : e * C ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hCC he0
  have hCe1 : e ≤ e * C ^ 4 := by nlinarith
  have hIA : ‖inflate p A‖ ≤ C + 1 := norm_inflate_le hp hp2 hnA hC0.le
  have hinner : ‖Agy - A * p * Bm‖ ≤ e + (C * e + 9 * e * C ^ 3) := by
    have hsplit : Agy - A * p * Bm = (Agy - A * Bm) + A * ((1 - p) * Bm) := by
      noncomm_ring
    rw [hsplit]
    have h2 : ‖(1 - p) * Bm‖ ≤ e + 9 * e * C ^ 2 := by
      have hd : (1 - p) * Bm = (Bm - M1 * Bm) + (M1 - p) * Bm := by noncomm_ring
      rw [hd]
      have ha : ‖Bm - M1 * Bm‖ ≤ e := by
        rw [show Bm - M1 * Bm = -(M1 * Bm - Bm) from by abel, norm_neg]
        exact hδB
      have hb : ‖(M1 - p) * Bm‖ ≤ 9 * e * C ^ 2 := by
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        have hb' : ‖M1 - p‖ ≤ 9 * e * C := by
          rw [show M1 - p = -(p - M1) from by abel, norm_neg]
          exact hη
        calc ‖M1 - p‖ * ‖Bm‖ ≤ (9 * e * C) * C :=
              mul_le_mul hb' hnB (norm_nonneg _) (by positivity)
          _ = 9 * e * C ^ 2 := by ring
      exact (norm_add_le _ _).trans (by linarith)
    have h3 : ‖A * ((1 - p) * Bm)‖ ≤ C * e + 9 * e * C ^ 3 := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      calc ‖A‖ * ‖(1 - p) * Bm‖ ≤ C * (e + 9 * e * C ^ 2) :=
            mul_le_mul hnA h2 (norm_nonneg _) hC0.le
        _ = C * e + 9 * e * C ^ 3 := by ring
    exact (norm_add_le _ _).trans (by linarith)
  have hstep2 : ‖inflate p Agy - inflate p A * inflate p Bm‖
      ≤ e + (C * e + 9 * e * C ^ 3) := by
    rw [inflate_mul p A Bm hp2]
    exact (norm_inflate_sub_inflate p _ _ hp hp2).trans hinner
  have hstep3 : ‖inflate p A * inflate p Bm - Ug * Uy‖
      ≤ (C + 1) * (4 * (21 * e * C ^ 3)) + 4 * (21 * e * C ^ 3) := by
    have hd : inflate p A * inflate p Bm - Ug * Uy
        = inflate p A * (inflate p Bm - Uy) + (inflate p A - Ug) * Uy := by
      noncomm_ring
    rw [hd]
    have ha : ‖inflate p A * (inflate p Bm - Uy)‖
        ≤ (C + 1) * (4 * (21 * e * C ^ 3)) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul hIA ?_ (norm_nonneg _) (by positivity)
      rw [show inflate p Bm - Uy = -(Uy - inflate p Bm) from by abel, norm_neg]
      exact hUy
    have hb : ‖(inflate p A - Ug) * Uy‖ ≤ 4 * (21 * e * C ^ 3) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      calc ‖inflate p A - Ug‖ * ‖Uy‖ ≤ (4 * (21 * e * C ^ 3)) * 1 := by
            refine mul_le_mul ?_ hUyn (norm_nonneg _) (by positivity)
            rw [show inflate p A - Ug = -(Ug - inflate p A) from by abel,
              norm_neg]
            exact hUg
        _ = 4 * (21 * e * C ^ 3) := by ring
    exact (norm_add_le _ _).trans (by linarith)
  have htri : ‖Ugy - Ug * Uy‖ ≤ ‖Ugy - inflate p Agy‖
      + ‖inflate p Agy - inflate p A * inflate p Bm‖
      + ‖inflate p A * inflate p Bm - Ug * Uy‖ := by
    have h3 : Ugy - Ug * Uy = (Ugy - inflate p Agy)
        + ((inflate p Agy - inflate p A * inflate p Bm)
          + (inflate p A * inflate p Bm - Ug * Uy)) := by abel
    rw [h3]
    have h1 := norm_add_le (Ugy - inflate p Agy)
      ((inflate p Agy - inflate p A * inflate p Bm)
        + (inflate p A * inflate p Bm - Ug * Uy))
    have h2 := norm_add_le (inflate p Agy - inflate p A * inflate p Bm)
      (inflate p A * inflate p Bm - Ug * Uy)
    linarith
  refine htri.trans ?_
  nlinarith

end Estimates

/-- **The separation estimate.**  The relative normalized trace of two
corrected unitaries is at most `400 e C⁴`, which at small accuracy is
below the `1/2` that forces operator distance `1`. -/
theorem sep_estimate (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    {p M1 A Bm Binv Agy Ug Uy : Matrix Y Y ℂ} {e C : ℝ}
    (hp : pᴴ = p) (hp2 : p * p = p) (hC1 : 1 ≤ C) (he0 : 0 ≤ e)
    (hnA : ‖A‖ ≤ C) (hnB : ‖Bm‖ ≤ C) (hn1 : ‖M1‖ ≤ C)
    (hη : ‖p - M1‖ ≤ 9 * e * C)
    (hstarB : ‖Binv - Bmᴴ‖ ≤ e)
    (hδBinv : ‖M1 * Binv - Binv‖ ≤ e)
    (hmulAB : ‖Agy - A * Binv‖ ≤ e)
    (htrAgy : ‖normTrace Y Agy‖ ≤ e)
    (htrM1 : ‖normTrace Y M1 - 1‖ ≤ e)
    (hUg : ‖Ug - inflate p A‖ ≤ 4 * (21 * e * C ^ 3))
    (hUy : ‖Uy - inflate p Bm‖ ≤ 4 * (21 * e * C ^ 3))
    (hUgn : ‖Ug‖ ≤ 1) :
    ‖normTrace Y (Ug * Uyᴴ)‖ ≤ 400 * e * C ^ 4 := by
  have hC0 : (0 : ℝ) < C := by linarith
  have hC3 : C ^ 3 ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hCC : C ≤ C ^ 4 := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hCone : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC1
  have hCe3 : e * C ^ 3 ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hC3 he0
  have hCe2 : e * C ^ 2 ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hC2 he0
  have hCeC : e * C ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hCC he0
  have hCe1 : e ≤ e * C ^ 4 := by nlinarith
  have hpn : ‖p‖ ≤ 1 := norm_proj_le_one hp hp2
  have hnBstar : ‖Bmᴴ‖ ≤ C := by rw [Matrix.l2_opNorm_conjTranspose]; exact hnB
  have hWprod : inflate p A * (inflate p Bm)ᴴ = inflate p (A * p * Bmᴴ) := by
    rw [inflate_conjTranspose p Bm hp, inflate_mul p A (Bmᴴ) hp2]
  have hIB : ‖(inflate p Bm)ᴴ‖ ≤ C + 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact norm_inflate_le hp hp2 hnB hC0.le
  have hUUclose : ‖Ug * Uyᴴ - inflate p A * (inflate p Bm)ᴴ‖
      ≤ 4 * (21 * e * C ^ 3) + (C + 1) * (4 * (21 * e * C ^ 3)) := by
    have hd : Ug * Uyᴴ - inflate p A * (inflate p Bm)ᴴ
        = Ug * (Uyᴴ - (inflate p Bm)ᴴ)
          + (Ug - inflate p A) * (inflate p Bm)ᴴ := by noncomm_ring
    rw [hd]
    have ha : ‖Ug * (Uyᴴ - (inflate p Bm)ᴴ)‖ ≤ 4 * (21 * e * C ^ 3) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      calc ‖Ug‖ * ‖Uyᴴ - (inflate p Bm)ᴴ‖ ≤ 1 * (4 * (21 * e * C ^ 3)) := by
            refine mul_le_mul hUgn ?_ (norm_nonneg _) zero_le_one
            rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
            exact hUy
        _ = 4 * (21 * e * C ^ 3) := by ring
    have hb : ‖(Ug - inflate p A) * (inflate p Bm)ᴴ‖
        ≤ (C + 1) * (4 * (21 * e * C ^ 3)) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      calc ‖Ug - inflate p A‖ * ‖(inflate p Bm)ᴴ‖
          ≤ (4 * (21 * e * C ^ 3)) * (C + 1) :=
            mul_le_mul hUg hIB (norm_nonneg _) (by positivity)
        _ = (C + 1) * (4 * (21 * e * C ^ 3)) := by ring
    exact (norm_add_le _ _).trans (by linarith)
  have hXnorm : ‖A * p * Bmᴴ‖ ≤ C ^ 2 := by
    calc ‖A * p * Bmᴴ‖ ≤ ‖A * p‖ * ‖Bmᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖A‖ * ‖p‖) * ‖Bmᴴ‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ (C * 1) * C :=
          mul_le_mul (mul_le_mul hnA hpn (norm_nonneg _) hC0.le) hnBstar
            (norm_nonneg _) (by positivity)
      _ = C ^ 2 := by ring
  have hcorner : ‖(p - 1) * Bmᴴ‖ ≤ 9 * e * C ^ 2 + C * e + 2 * e := by
    have hd : (p - 1) * Bmᴴ
        = (p - M1) * Bmᴴ
          + (M1 * (Bmᴴ - Binv) + ((M1 * Binv - Binv) + (Binv - Bmᴴ))) := by
      noncomm_ring
    rw [hd]
    have h1 : ‖(p - M1) * Bmᴴ‖ ≤ 9 * e * C ^ 2 := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      calc ‖p - M1‖ * ‖Bmᴴ‖ ≤ (9 * e * C) * C :=
            mul_le_mul hη hnBstar (norm_nonneg _) (by positivity)
        _ = 9 * e * C ^ 2 := by ring
    have h2 : ‖M1 * (Bmᴴ - Binv)‖ ≤ C * e := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul hn1 ?_ (norm_nonneg _) hC0.le
      rw [show Bmᴴ - Binv = -(Binv - Bmᴴ) from by abel, norm_neg]
      exact hstarB
    have h34 := (norm_add_le (M1 * Binv - Binv) (Binv - Bmᴴ)).trans
      (by linarith : ‖M1 * Binv - Binv‖ + ‖Binv - Bmᴴ‖ ≤ e + e)
    have h234 := (norm_add_le (M1 * (Bmᴴ - Binv))
      ((M1 * Binv - Binv) + (Binv - Bmᴴ))).trans
      (by linarith : ‖M1 * (Bmᴴ - Binv)‖
        + ‖(M1 * Binv - Binv) + (Binv - Bmᴴ)‖ ≤ C * e + (e + e))
    exact (norm_add_le _ _).trans (by linarith)
  have hXclose : ‖A * p * Bmᴴ - Agy‖
      ≤ C * (9 * e * C ^ 2 + C * e + 2 * e) + (C * e + e) := by
    have hd : A * p * Bmᴴ - Agy
        = A * ((p - 1) * Bmᴴ) + (A * (Bmᴴ - Binv) + (A * Binv - Agy)) := by
      noncomm_ring
    rw [hd]
    have t1 : ‖A * ((p - 1) * Bmᴴ)‖ ≤ C * (9 * e * C ^ 2 + C * e + 2 * e) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      exact mul_le_mul hnA hcorner (norm_nonneg _) hC0.le
    have t2 : ‖A * (Bmᴴ - Binv)‖ ≤ C * e := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul hnA ?_ (norm_nonneg _) hC0.le
      rw [show Bmᴴ - Binv = -(Binv - Bmᴴ) from by abel, norm_neg]
      exact hstarB
    have t3 : ‖A * Binv - Agy‖ ≤ e := by
      rw [show A * Binv - Agy = -(Agy - A * Binv) from by abel, norm_neg]
      exact hmulAB
    have t23 := (norm_add_le (A * (Bmᴴ - Binv)) (A * Binv - Agy)).trans
      (by linarith : ‖A * (Bmᴴ - Binv)‖ + ‖A * Binv - Agy‖ ≤ C * e + e)
    exact (norm_add_le _ _).trans (by linarith)
  have htrX : ‖normTrace Y (A * p * Bmᴴ)‖
      ≤ e + (C * (9 * e * C ^ 2 + C * e + 2 * e) + (C * e + e)) := by
    have hd : normTrace Y (A * p * Bmᴴ)
        = normTrace Y Agy + normTrace Y (A * p * Bmᴴ - Agy) := by
      rw [normTrace_sub]; ring
    rw [hd]
    have h2 := (norm_normTrace_le Y hY (A * p * Bmᴴ - Agy)).trans hXclose
    exact (norm_add_le _ _).trans (by linarith)
  have hcodim : (Matrix.trace ((1 : Matrix Y Y ℂ) - p)).re
        / (Fintype.card Y : ℝ) ≤ e + 9 * e * C :=
    codimension_weight_le Y hY htrM1 hη
  have hwnn : (0 : ℝ) ≤ e + 9 * e * C := by nlinarith
  have hinflTr : ‖normTrace Y (inflate p (A * p * Bmᴴ))
        - normTrace Y (A * p * Bmᴴ)‖ ≤ (1 + 3 * C ^ 2) * (e + 9 * e * C) := by
    have hbase := norm_normTrace_inflate_sub Y hp hp2 (A * p * Bmᴴ)
    rw [mul_div_assoc] at hbase
    refine hbase.trans ?_
    calc (1 + 3 * ‖A * p * Bmᴴ‖)
          * ((Matrix.trace ((1 : Matrix Y Y ℂ) - p)).re
            / (Fintype.card Y : ℝ))
        ≤ (1 + 3 * ‖A * p * Bmᴴ‖) * (e + 9 * e * C) :=
          mul_le_mul_of_nonneg_left hcodim (by positivity)
      _ ≤ (1 + 3 * C ^ 2) * (e + 9 * e * C) :=
          mul_le_mul_of_nonneg_right (by linarith) hwnn
  have hlast : ‖normTrace Y (Ug * Uyᴴ - inflate p (A * p * Bmᴴ))‖
      ≤ 4 * (21 * e * C ^ 3) + (C + 1) * (4 * (21 * e * C ^ 3)) := by
    refine (norm_normTrace_le Y hY _).trans ?_
    rw [← hWprod]
    exact hUUclose
  have hsplit : normTrace Y (Ug * Uyᴴ)
      = (normTrace Y (inflate p (A * p * Bmᴴ))
          - normTrace Y (A * p * Bmᴴ))
        + (normTrace Y (A * p * Bmᴴ)
          + normTrace Y (Ug * Uyᴴ - inflate p (A * p * Bmᴴ))) := by
    rw [normTrace_sub]
    ring
  rw [hsplit]
  have hinner := norm_add_le (normTrace Y (A * p * Bmᴴ))
    (normTrace Y (Ug * Uyᴴ - inflate p (A * p * Bmᴴ)))
  refine (norm_add_le _ _).trans ?_
  nlinarith

/-- **MF-trace recognition.**  If the regular character of a group is an
MF trace, the group is operator MF: the corner-and-polar correction of
any trace-correct model family produces operator-norm local models with
separation constant `1`.

The trace clause does all the work the weak definition cannot: at `1` it
pins the unit corner at relative dimension one, and at `g ≠ 1` it gives
separation `√2 - o(1) > 1` automatically. -/
theorem isNormApproximable_of_isMFRegularCharacter
    (h : IsMFRegularCharacter G) : IsNormApproximable G 1 := by
  classical
  obtain ⟨Bnd, hB⟩ := h
  intro F ε hε
  -- The test set, closed under everything the two clauses touch.
  set F₀ : Finset G := insert 1 ((F ∪ F.image (fun x => x⁻¹)) ∪
      ((F ×ˢ F).image (fun q => q.1 * q.2) ∪
        (F ×ˢ F).image (fun q => q.1 * q.2⁻¹))) with hF₀def
  set F' : Finset G := F₀ ∪ F₀.image (fun x => x⁻¹) with hF'def
  have hsub₀ : F₀ ⊆ F' := Finset.subset_union_left
  have h1F' : (1 : G) ∈ F' := hsub₀ (Finset.mem_insert_self _ _)
  have hFF' : ∀ g ∈ F, g ∈ F' := fun g hg =>
    hsub₀ (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ hg)))
  have hmulF' : ∀ g ∈ F, ∀ y ∈ F, g * y ∈ F' := fun g hg y hy =>
    hsub₀ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(g, y), Finset.mem_product.mpr ⟨hg, hy⟩, rfl⟩))))
  have hdivF' : ∀ g ∈ F, ∀ y ∈ F, g * y⁻¹ ∈ F' := fun g hg y hy =>
    hsub₀ (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(g, y), Finset.mem_product.mpr ⟨hg, hy⟩, rfl⟩))))
  have hinvF' : ∀ x ∈ F', x⁻¹ ∈ F' := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      simpa using hsub₀ hz
  -- A uniform norm bound on the test set: a sum dominates each of its
  -- nonnegative terms, which is cheaper here than a maximum.
  set C : ℝ := (∑ g ∈ F', |Bnd g|) + 1 with hCdef
  have hCsum : (0 : ℝ) ≤ ∑ g ∈ F', |Bnd g| :=
    Finset.sum_nonneg fun g _ => abs_nonneg _
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; linarith
  have hC0 : (0 : ℝ) < C := by linarith
  have hC3 : C ^ 3 ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hCC : C ≤ C ^ 4 := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
  have hCone : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC1
  -- the accuracy
  set e : ℝ := min 1 (min (ε / (400 * C ^ 4)) (1 / (1000 * C ^ 4))) with hedef
  have he1 : e ≤ 1 := min_le_left _ _
  have hea : e ≤ ε / (400 * C ^ 4) := (min_le_right _ _).trans (min_le_left _ _)
  have heb : e ≤ 1 / (1000 * C ^ 4) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have he0 : 0 < e := by
    rw [hedef]
    exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have heps : 400 * e * C ^ 4 ≤ ε := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 400 * C ^ 4)] at hea
    nlinarith
  have hsmall : 1000 * e * C ^ 4 ≤ 1 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 1000 * C ^ 4)] at heb
    nlinarith
  have hCe3 : e * C ^ 3 ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hC3 he0.le
  have hCe2 : e * C ^ 2 ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hC2 he0.le
  have hCeC : e * C ≤ e * C ^ 4 := mul_le_mul_of_nonneg_left hCC he0.le
  have hCe1 : e ≤ e * C ^ 4 := by nlinarith
  -- the model
  obtain ⟨M⟩ := hB F' e he0
  obtain ⟨Y, hYpos, mp, hbdd, hmul, hstar, htr1, htrne⟩ := M
  set p : Matrix Y Y ℂ := unitProjection (mp 1) with hpdef
  have hp : pᴴ = p := by
    rw [hpdef]; exact (unitProjection_isOrthogonalProjection (mp 1)).1
  have hp2 : p * p = p := by
    rw [hpdef]; exact (unitProjection_isOrthogonalProjection (mp 1)).2
  have hbound : ∀ g ∈ F', ‖mp g‖ ≤ C := by
    intro g hg
    refine (hbdd g hg).trans ?_
    have h2 : |Bnd g| ≤ ∑ x ∈ F', |Bnd x| :=
      Finset.single_le_sum (f := fun x => |Bnd x|)
        (fun x _ => abs_nonneg (Bnd x)) hg
    have h1 : Bnd g ≤ |Bnd g| := le_abs_self _
    rw [hCdef]
    linarith
  have hnorm1 : ‖mp 1‖ ≤ C := hbound 1 h1F'
  have hstar1 : ‖mp 1 - (mp 1)ᴴ‖ ≤ e := by
    have hs := hstar 1 h1F'
    rwa [inv_one] at hs
  have hidem1 : ‖mp 1 * mp 1 - mp 1‖ ≤ e := by
    have hm := hmul 1 h1F' 1 h1F'
    rw [mul_one] at hm
    rw [show mp 1 * mp 1 - mp 1 = -(mp 1 - mp 1 * mp 1) from by abel, norm_neg]
    exact hm
  have hη : ‖p - mp 1‖ ≤ 9 * e * C := by
    rw [hpdef]
    exact norm_unitProjection_sub_le hstar1 hidem1 hnorm1 he0.le he1 hC1
  have hδ₁ : ∀ g ∈ F', ‖mp 1 * mp g - mp g‖ ≤ e := by
    intro g hg
    have hm := hmul 1 h1F' g hg
    rw [one_mul] at hm
    rw [show mp 1 * mp g - mp g = -(mp g - mp 1 * mp g) from by abel, norm_neg]
    exact hm
  have hmulinv : ∀ g ∈ F', ‖mp 1 - mp g⁻¹ * mp g‖ ≤ e := by
    intro g hg
    have hm := hmul g⁻¹ (hinvF' g hg) g hg
    rwa [inv_mul_cancel] at hm
  -- the corrected unitaries
  have hΔhalf : 21 * e * C ^ 3 ≤ 1 / 2 := by nlinarith
  have hexists : ∀ g ∈ F', ∃ U ∈ Matrix.unitaryGroup Y ℂ,
      ‖U - inflate p (mp g)‖ ≤ 4 * (21 * e * C ^ 3) := by
    intro g hg
    refine exists_unitary_near_inflate p (mp g) hp hp2 (by positivity) hΔhalf ?_
    exact corner_defect_le hp hp2 (hbound g hg) hC1 he0.le hη (hδ₁ g hg)
      (hstar g hg) (hmulinv g hg)
  choose! U hUmem hUnear using hexists
  refine ⟨{
    carrier := Y
    nonempty := hYpos
    map := fun g => if g ∈ F' then U g else 1
    isUnitary := ?_
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g
    by_cases hg : g ∈ F'
    · rw [if_pos hg]; exact hUmem g hg
    · rw [if_neg hg]; exact one_mem _
  · intro g hg y hy
    have hgF := hFF' g hg
    have hyF := hFF' y hy
    have hgyF := hmulF' g hg y hy
    rw [if_pos hgF, if_pos hyF, if_pos hgyF]
    refine (mult_estimate hp hp2 hC1 he0.le (hbound g hgF) (hbound y hyF) hη
      (hmul g hgF y hyF) (hδ₁ y hyF) (hUnear g hgF) (hUnear y hyF)
      (hUnear (g * y) hgyF) (norm_unitary_le_one (hUmem y hyF))).trans ?_
    linarith
  · intro g hg y hy hne
    have hgF := hFF' g hg
    have hyF := hFF' y hy
    have hyinvF := hinvF' y hyF
    rw [if_pos hgF, if_pos hyF]
    refine one_le_norm_sub_of_normTrace_small Y (hUmem g hgF) (hUmem y hyF)
      hYpos ?_
    refine (sep_estimate Y hYpos hp hp2 hC1 he0.le (hbound g hgF)
      (hbound y hyF) hnorm1 hη (hstar y hyF) (hδ₁ y⁻¹ hyinvF)
      (hmul g hgF y⁻¹ hyinvF)
      (htrne (g * y⁻¹) (hdivF' g hg y hy)
        (fun hcon => hne (mul_inv_eq_one.mp hcon)))
      (htr1 h1F') (hUnear g hgF) (hUnear y hyF)
      (norm_unitary_le_one (hUmem g hgF))).trans ?_
    linarith
