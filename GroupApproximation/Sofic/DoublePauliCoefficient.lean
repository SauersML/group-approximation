import GroupApproximation.Sofic.ExactInvolutionCut

/-!
# Cancelling two Pauli shifts into a coefficient involution

If two involutions both anticommute with the same Pauli coordinate, their
product commutes with that coordinate.  When the two involutions commute,
their product is again an involution and also commutes with each factor.
This is the algebraic core of the raw double-Pauli coefficient packet.
-/

namespace GroupApproximation

open Matrix

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- The product of two operators carrying the same Pauli sign commutes with
the Pauli coordinate. -/
theorem product_commutes_of_both_anticommute
    (X C Z : Matrix Y Y ℂ)
    (hXZ : X * Z = -(Z * X)) (hCZ : C * Z = -(Z * C)) :
    (X * C) * Z = Z * (X * C) := by
  calc
    (X * C) * Z = X * (C * Z) := by rw [Matrix.mul_assoc]
    _ = X * (-(Z * C)) := by rw [hCZ]
    _ = -(X * Z) * C := by noncomm_ring
    _ = -(-(Z * X)) * C := by rw [hXZ]
    _ = Z * (X * C) := by noncomm_ring

/-- Commuting involutions multiply to an involution. -/
theorem product_sq_one_of_commuting_involutions
    (X C : Matrix Y Y ℂ)
    (hXsq : X * X = 1) (hCsq : C * C = 1) (hXC : X * C = C * X) :
    (X * C) * (X * C) = 1 := by
  calc
    (X * C) * (X * C) = X * (C * X) * C := by noncomm_ring
    _ = X * (X * C) * C := by rw [← hXC]
    _ = (X * X) * (C * C) := by noncomm_ring
    _ = 1 := by rw [hXsq, hCsq, Matrix.one_mul]

omit [DecidableEq Y] in
/-- The cancelled product belongs to the commutant of its first factor. -/
theorem product_commutes_left_of_commuting_involution
    (X C : Matrix Y Y ℂ) (hXC : X * C = C * X) :
    (X * C) * X = X * (X * C) := by
  calc
    (X * C) * X = X * (C * X) := by noncomm_ring
    _ = X * (X * C) := by rw [← hXC]

omit [DecidableEq Y] in
/-- The cancelled product belongs to the commutant of its second factor. -/
theorem product_commutes_right_of_commuting_involution
    (X C : Matrix Y Y ℂ) (hXC : X * C = C * X) :
    (X * C) * C = C * (X * C) := by
  calc
    (X * C) * C = X * (C * C) := by noncomm_ring
    _ = (X * C) * C := by noncomm_ring
    _ = (C * X) * C := by rw [hXC]
    _ = C * (X * C) := by noncomm_ring

/-- Glue the `A` coefficient on the `P` sheet to the `X` coefficient on the
complementary sheet.  This is the algebraic two-sheet splice exposed by the
raw double-Pauli packet. -/
def twoSheetCoefficient (P X A : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  P * A + (1 - P) * X

/-- A sheet swap which exchanges `X` with `A` fixes their two-sheet splice. -/
theorem twoSheetCoefficient_conj_eq_self
    (P X A R : Matrix Y Y ℂ)
    (hRsq : R * R = 1)
    (hRP : R * P * R = 1 - P)
    (hRX : R * X * R = A)
    (hRA : R * A * R = X) :
    R * twoSheetCoefficient P X A * R =
      twoSheetCoefficient P X A := by
  have hRcomp : R * (1 - P) * R = P := by
    calc
      R * (1 - P) * R = R * R - R * P * R := by noncomm_ring
      _ = 1 - (1 - P) := by rw [hRsq, hRP]
      _ = P := by module
  have hconjPA : R * (P * A) * R =
      (R * P * R) * (R * A * R) := by
    calc
      R * (P * A) * R = R * P * (R * R) * A * R := by
        rw [hRsq, Matrix.mul_one]
        noncomm_ring
      _ = (R * P * R) * (R * A * R) := by noncomm_ring
  have hconjCompX : R * ((1 - P) * X) * R =
      (R * (1 - P) * R) * (R * X * R) := by
    calc
      R * ((1 - P) * X) * R =
          R * (1 - P) * (R * R) * X * R := by
            rw [hRsq, Matrix.mul_one]
            noncomm_ring
      _ = (R * (1 - P) * R) * (R * X * R) := by noncomm_ring
  unfold twoSheetCoefficient
  calc
    R * (P * A + (1 - P) * X) * R =
        R * (P * A) * R + R * ((1 - P) * X) * R := by
          rw [Matrix.mul_add, Matrix.add_mul]
    _ = (R * P * R) * (R * A * R) +
          (R * (1 - P) * R) * (R * X * R) := by
            rw [hconjPA, hconjCompX]
    _ = (1 - P) * X + P * A := by rw [hRP, hRA, hRcomp, hRX]
    _ = P * A + (1 - P) * X := by abel

/-- Sheetwise commutation is enough for the glued coefficient to commute
globally.  The hypotheses are deliberately localized: neither `A` nor `X`
has to commute with `Z` off its selected sheet. -/
theorem twoSheetCoefficient_commutes_of_sheetwise
    (P X A Z : Matrix Y Y ℂ)
    (hPZ : P * Z = Z * P)
    (hA : P * (A * Z - Z * A) = 0)
    (hX : (1 - P) * (X * Z - Z * X) = 0) :
    twoSheetCoefficient P X A * Z =
      Z * twoSheetCoefficient P X A := by
  have hcompZ : (1 - P) * Z = Z * (1 - P) := by
    calc
      (1 - P) * Z = Z - P * Z := by noncomm_ring
      _ = Z - Z * P := by rw [hPZ]
      _ = Z * (1 - P) := by noncomm_ring
  have hPA : (P * A) * Z = Z * (P * A) := by
    have hAeq : P * (A * Z) = P * (Z * A) := by
      apply sub_eq_zero.mp
      rw [← Matrix.mul_sub]
      exact hA
    calc
      (P * A) * Z = P * (A * Z) := by rw [Matrix.mul_assoc]
      _ = P * (Z * A) := hAeq
      _ = (P * Z) * A := by rw [Matrix.mul_assoc]
      _ = (Z * P) * A := by rw [hPZ]
      _ = Z * (P * A) := by rw [Matrix.mul_assoc]
  have hcompX : ((1 - P) * X) * Z = Z * ((1 - P) * X) := by
    have hXeq : (1 - P) * (X * Z) = (1 - P) * (Z * X) := by
      apply sub_eq_zero.mp
      rw [← Matrix.mul_sub]
      exact hX
    calc
      ((1 - P) * X) * Z = (1 - P) * (X * Z) := by rw [Matrix.mul_assoc]
      _ = (1 - P) * (Z * X) := hXeq
      _ = ((1 - P) * Z) * X := by rw [Matrix.mul_assoc]
      _ = (Z * (1 - P)) * X := by rw [hcompZ]
      _ = Z * ((1 - P) * X) := by rw [Matrix.mul_assoc]
  unfold twoSheetCoefficient
  rw [Matrix.add_mul, Matrix.mul_add, hPA, hcompX]

/-- If the two sheets reduce two involutions, their splice is again an
involution. -/
theorem twoSheetCoefficient_sq_one
    (P X A : Matrix Y Y ℂ)
    (hPid : P * P = P)
    (hPX : P * X = X * P)
    (hPA : P * A = A * P)
    (hXsq : X * X = 1)
    (hAsq : A * A = 1) :
    twoSheetCoefficient P X A * twoSheetCoefficient P X A = 1 := by
  have hPAsq : (P * A) * (P * A) = P := by
    calc
      (P * A) * (P * A) = P * (A * P) * A := by
        simp only [Matrix.mul_assoc]
      _ = P * (P * A) * A := by rw [← hPA]
      _ = (P * P) * (A * A) := by noncomm_ring
      _ = P := by rw [hPid, hAsq, Matrix.mul_one]
  have hcompId : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hPid]
  have hcompX : (1 - P) * X = X * (1 - P) := by
    noncomm_ring [hPX]
  have hcompXsq : ((1 - P) * X) * ((1 - P) * X) = 1 - P := by
    calc
      ((1 - P) * X) * ((1 - P) * X) =
          (1 - P) * (X * (1 - P)) * X := by
            simp only [Matrix.mul_assoc]
      _ = (1 - P) * ((1 - P) * X) * X := by rw [← hcompX]
      _ = ((1 - P) * (1 - P)) * (X * X) := by noncomm_ring
      _ = 1 - P := by rw [hcompId, hXsq, Matrix.mul_one]
  have hPcomp : P * (1 - P) = 0 := by
    noncomm_ring [hPid]
  have hcompP : (1 - P) * P = 0 := by
    noncomm_ring [hPid]
  have hAcomp : A * (1 - P) = (1 - P) * A := by
    noncomm_ring [hPA]
  have hcrossLeft : (P * A) * ((1 - P) * X) = 0 := by
    calc
      (P * A) * ((1 - P) * X) = P * (A * (1 - P)) * X := by
        simp only [Matrix.mul_assoc]
      _ = P * ((1 - P) * A) * X := by rw [hAcomp]
      _ = (P * (1 - P)) * (A * X) := by noncomm_ring
      _ = 0 := by rw [hPcomp, Matrix.zero_mul]
  have hcrossRight : ((1 - P) * X) * (P * A) = 0 := by
    calc
      ((1 - P) * X) * (P * A) = (1 - P) * (X * P) * A := by
        simp only [Matrix.mul_assoc]
      _ = (1 - P) * (P * X) * A := by rw [← hPX]
      _ = ((1 - P) * P) * (X * A) := by noncomm_ring
      _ = 0 := by rw [hcompP, Matrix.zero_mul]
  unfold twoSheetCoefficient
  calc
    (P * A + (1 - P) * X) * (P * A + (1 - P) * X) =
        (P * A) * (P * A) + (P * A) * ((1 - P) * X) +
          (((1 - P) * X) * (P * A) +
            ((1 - P) * X) * ((1 - P) * X)) := by noncomm_ring
    _ = P + 0 + (0 + (1 - P)) := by
      rw [hPAsq, hcrossLeft, hcrossRight, hcompXsq]
    _ = 1 := by module

/-- For two orthogonal projections, the squared Hilbert--Schmidt mass of the
transition block is the real part of their tracial overlap.  This converts
the exact `1/64` double-Pauli overlap table into a fixed block-mass table. -/
theorem hsNormSq_projection_product_eq_re_normTrace
    (Y : FiniteModel) (P Q : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hQstar : Qᴴ = Q) (hQid : Q * Q = Q) :
    hsNormSq Y (P * Q) = (normTrace Y (P * Q)).re := by
  have htrace :
      normTrace Y ((P * Q) * (P * Q)ᴴ) = normTrace Y (P * Q) := by
    unfold normTrace
    rw [Matrix.conjTranspose_mul, hPstar, hQstar]
    congr 1
    have hmul : (P * Q) * (Q * P) = (P * Q) * P := by
      calc
        (P * Q) * (Q * P) = P * (Q * Q) * P := by noncomm_ring
        _ = P * Q * P := by rw [hQid]
        _ = (P * Q) * P := by rfl
    calc
      Matrix.trace ((P * Q) * (Q * P)) =
          Matrix.trace ((P * Q) * P) := by rw [hmul]
      _ = Matrix.trace (P * (P * Q)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * Q) := by rw [← Matrix.mul_assoc, hPid]
  have hcomplex := ofReal_hsNormSq Y (P * Q)
  rw [htrace] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa using hreal

/-- Squared Hilbert--Schmidt distance between two projections, expressed by
their three tracial overlaps. -/
theorem hsDistSq_projections_eq_re_normTrace
    (Y : FiniteModel) (P Q : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hQstar : Qᴴ = Q) (hQid : Q * Q = Q) :
    hsDistSq Y P Q =
      (normTrace Y P).re + (normTrace Y Q).re -
        2 * (normTrace Y (P * Q)).re := by
  change hsNormSq Y (P - Q) = _
  have hproduct : (P - Q) * (P - Q)ᴴ =
      P + Q - P * Q - Q * P := by
    rw [Matrix.conjTranspose_sub, hPstar, hQstar]
    noncomm_ring [hPid, hQid]
  have htrace :
      normTrace Y (P + Q - P * Q - Q * P) =
        normTrace Y P + normTrace Y Q - 2 * normTrace Y (P * Q) := by
    unfold normTrace
    rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_mul_comm Q P]
    ring
  have hcomplex := ofReal_hsNormSq Y (P - Q)
  rw [hproduct, htrace] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa using hreal

/-- A trace-`1/8` projection and a trace-`1/8` projection with overlap
`1/64` are separated by the fixed squared distance `7/32`. -/
theorem hsDistSq_projections_eq_seven_div_thirty_two
    (Y : FiniteModel) (P Q : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hQstar : Qᴴ = Q) (hQid : Q * Q = Q)
    (hPtrace : normTrace Y P = (8 : ℂ)⁻¹)
    (hQtrace : normTrace Y Q = (8 : ℂ)⁻¹)
    (hoverlap : normTrace Y (P * Q) = (64 : ℂ)⁻¹) :
    hsDistSq Y P Q = (7 : ℝ) / 32 := by
  rw [hsDistSq_projections_eq_re_normTrace Y P Q
    hPstar hPid hQstar hQid, hPtrace, hQtrace, hoverlap]
  norm_num

/-- The anti-normalizer gap has a strict `1/8` safety margin.  Thus any
coordinate-alignment theorem producing squared distance at most `1/8`
already contradicts the trace-flat moments; convergence all the way to zero
is unnecessary. -/
theorem one_eighth_lt_hsDistSq_of_trace_flat_projections
    (Y : FiniteModel) (P Q : Matrix Y Y ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hQstar : Qᴴ = Q) (hQid : Q * Q = Q)
    (hPtrace : normTrace Y P = (8 : ℂ)⁻¹)
    (hQtrace : normTrace Y Q = (8 : ℂ)⁻¹)
    (hoverlap : normTrace Y (P * Q) = (64 : ℂ)⁻¹) :
    (1 : ℝ) / 8 < hsDistSq Y P Q := by
  rw [hsDistSq_projections_eq_seven_div_thirty_two Y P Q
    hPstar hPid hQstar hQid hPtrace hQtrace hoverlap]
  norm_num

/-- The trace-flat transported cut stays a fixed distance from its
Hilbert--Schmidt conditional expectation onto the raw four-character
coefficient algebra.  The expectation is `Q/8`, and the squared residual is
`15/128`. -/
theorem hsNormSq_projection_sub_eighth_carrier_eq_fifteen_div_128
    (Y : FiniteModel) (G Q : Matrix Y Y ℂ)
    (hGstar : Gᴴ = G) (hGid : G * G = G)
    (hQstar : Qᴴ = Q) (hQid : Q * Q = Q)
    (hGtrace : normTrace Y G = (8 : ℂ)⁻¹)
    (hQtrace : normTrace Y Q = (2 : ℂ)⁻¹)
    (hoverlap : normTrace Y (G * Q) = (16 : ℂ)⁻¹) :
    hsNormSq Y (G - (8 : ℂ)⁻¹ • Q) = (15 : ℝ) / 128 := by
  let a : ℂ := (8 : ℂ)⁻¹
  have hastar : (G - a • Q)ᴴ = G - a • Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hGstar, hQstar]
    norm_num [a]
  have hproduct : (G - a • Q) * (G - a • Q)ᴴ =
      G - a • (G * Q) - a • (Q * G) + (a * a) • Q := by
    rw [hastar]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hGid, hQid]
    module
  have hQGtrace : normTrace Y (Q * G) = (16 : ℂ)⁻¹ := by
    unfold normTrace at hoverlap ⊢
    rw [Matrix.trace_mul_comm Q G]
    exact hoverlap
  have htrace :
      normTrace Y
          (G - a • (G * Q) - a • (Q * G) + (a * a) • Q) =
        (15 : ℂ) / 128 := by
    have ntAdd (A B : Matrix Y Y ℂ) :
        normTrace Y (A + B) = normTrace Y A + normTrace Y B := by
      unfold normTrace
      rw [Matrix.trace_add, add_div]
    have ntSub (A B : Matrix Y Y ℂ) :
        normTrace Y (A - B) = normTrace Y A - normTrace Y B := by
      unfold normTrace
      rw [Matrix.trace_sub, sub_div]
    have ntSmul (b : ℂ) (A : Matrix Y Y ℂ) :
        normTrace Y (b • A) = b * normTrace Y A := by
      unfold normTrace
      rw [Matrix.trace_smul]
      simp only [smul_eq_mul]
      ring
    rw [ntAdd, ntSub, ntSub, ntSmul, ntSmul, ntSmul,
      hGtrace, hoverlap, hQGtrace, hQtrace]
    norm_num [a]
  have hcomplex := ofReal_hsNormSq Y (G - a • Q)
  rw [hproduct, htrace] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  norm_num at hreal ⊢
  exact hreal

/-- The transported-Pauli orbit average has a canonical raw-coordinate
fingerprint.  If its coefficient expectation has weights
`75/256, 31/256, 15/256`, then the uniquely top-weighted cut is recovered by
one fixed quadratic polynomial.  The third idempotent may be the sum of the
two bottom character cuts. -/
theorem recover_top_cut_from_pauli_orbit_fingerprint
    (Ftop Fmiddle Fbottom : Matrix Y Y ℂ)
    (htop : Ftop * Ftop = Ftop)
    (hmiddle : Fmiddle * Fmiddle = Fmiddle)
    (hbottom : Fbottom * Fbottom = Fbottom)
    (htm : Ftop * Fmiddle = 0) (hmt : Fmiddle * Ftop = 0)
    (htb : Ftop * Fbottom = 0) (hbt : Fbottom * Ftop = 0)
    (hmb : Fmiddle * Fbottom = 0) (hbm : Fbottom * Fmiddle = 0) :
    let Q := Ftop + Fmiddle + Fbottom
    let S := ((75 : ℂ) / 256) • Ftop +
      ((31 : ℂ) / 256) • Fmiddle + ((15 : ℂ) / 256) • Fbottom
    ((4096 : ℂ) / 165) •
        ((S - ((31 : ℂ) / 256) • Q) *
          (S - ((15 : ℂ) / 256) • Q)) = Ftop := by
  dsimp
  noncomm_ring [htop, hmiddle, hbottom, htm, hmt, htb, hbt, hmb, hbm]
  simp
  module

/-- Arithmetic core of the trace-flat spectral truncation.  A positive
contraction of total normalized trace `1/64`, supported on trace `1/8`, has
at least trace `1/120` above eigenvalue `1/16`.  `lowMass` and `highMass`
are the two spectral contributions; the spectral theorem supplies the two
displayed upper bounds. -/
theorem one_div_120_le_of_trace_flat_spectral_split
    (lowMass highMass retainedTrace : ℝ)
    (hsplit : lowMass + highMass = (1 : ℝ) / 64)
    (hlow : lowMass ≤ (1 : ℝ) / 16 * ((1 : ℝ) / 8 - retainedTrace))
    (hhigh : highMass ≤ retainedTrace) :
    (1 : ℝ) / 120 ≤ retainedTrace := by
  norm_num at hsplit hlow ⊢
  linarith

end GroupApproximation
