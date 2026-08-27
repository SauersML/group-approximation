import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Quasidiagonal compressions: the analytic core of `INT.11`'s reduction

## The ledger row, and what this module is

`INT.11` prints *"all amenable groups are MF, by quasidiagonality"* --- the
Tikuisis--White--Winter theorem, a literature input this development does
not formalize.  The *reduction* half of that sentence --- quasidiagonal
(separable, faithfully represented) algebras are MF --- is elementary by
comparison, and its analytic core is proved here:

* `IsQuasidiagonalSequence` --- a sequence of finite-rank orthogonal
  projections asymptotically commuting with a representation and converging
  strongly to the identity: the operational form of quasidiagonality of a
  representation on a separable space.
* `norm_apply_le_of_projection` --- a selfadjoint idempotent is a
  contraction.
* `compression_asymptotically_multiplicative` --- the compressions
  `a ↦ Pₙ π(a) Pₙ` are asymptotically multiplicative:
  `‖Pₙπ(a)Pₙ · Pₙπ(b)Pₙ − Pₙπ(ab)Pₙ‖ → 0`, with the single commutator
  estimate `P a P b P - P (ab) P = P a (P b - b P) P`.
* `tendsto_compression_apply` --- the compressions converge strongly to the
  representation.
* `eq_zero_of_tendsto_compression_norm` --- an element whose compressions
  vanish in norm is killed by the representation; with faithfulness, the
  compression sequence separates points.  This is the injectivity engine
  for a corona embedding.

## What remains for the row

Two things, of different kinds.  The *matrix-coordinate assembly*: choosing
orthonormal bases of the ranges `Pₙ H` identifies the compressions with a
bounded matrix sequence, and the three theorems above say exactly that its
corona class is a faithful ⋆-homomorphism --- turning that into a
`HasMFEmbedding` witness against `NormMatrixCStarCorona` is bookkeeping
against the corona's coordinate conventions, not analysis, and is left to a
follow-up wave.  The *TWW input*: that amenable groups admit quasidiagonal
representations at all is the literature input, which stays a typed
hypothesis wherever it is consumed; nothing here or downstream may
transcribe it.  `INT.11` remains `MISSING`/`literature-input` as recorded.
-/

namespace GroupApproximation
namespace Quasidiagonal

open scoped InnerProductSpace
open Filter

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem re_inner_self' {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (v : V) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) v
  simpa [RCLike.re_to_complex] using h

/-- A selfadjoint idempotent bounded operator is a contraction. -/
theorem norm_apply_le_of_projection {P : H →L[ℂ] H}
    (hidem : IsIdempotentElem P) (hsa : IsSelfAdjoint P) (v : H) :
    ‖P v‖ ≤ ‖v‖ := by
  rcases eq_or_ne (P v) 0 with h0 | h0
  · rw [h0, norm_zero]
    exact norm_nonneg v
  · have h1 : ‖P v‖ ^ 2 = (⟪v, P v⟫_ℂ).re := by
      have e1 : ⟪P v, P v⟫_ℂ = ⟪v, P (P v)⟫_ℂ := by
        have e2 : star P = P := hsa.star_eq
        calc ⟪P v, P v⟫_ℂ
            = ⟪v, (ContinuousLinearMap.adjoint P) (P v)⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪v, P (P v)⟫_ℂ := by
              rw [← ContinuousLinearMap.star_eq_adjoint, e2]
      have e3 : P (P v) = P v := by
        have e4 : P * P = P := hidem.eq
        rw [← mul_apply_eq_comp, e4]
      rw [← re_inner_self' (P v), e1, e3]
    have h2 : (⟪v, P v⟫_ℂ).re ≤ ‖v‖ * ‖P v‖ := by
      calc (⟪v, P v⟫_ℂ).re ≤ ‖⟪v, P v⟫_ℂ‖ := Complex.re_le_norm _
        _ ≤ ‖v‖ * ‖P v‖ := norm_inner_le_norm _ _
    have h3 : 0 < ‖P v‖ := norm_pos_iff.mpr h0
    nlinarith

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **A quasidiagonalizing sequence** for a representation: finite-rank
orthogonal projections, asymptotically commuting with the image,
converging strongly to the identity. -/
structure IsQuasidiagonalSequence (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (P : ℕ → H →L[ℂ] H) : Prop where
  /-- Each term is idempotent. -/
  idem : ∀ n, IsIdempotentElem (P n)
  /-- Each term is selfadjoint. -/
  selfadjoint : ∀ n, IsSelfAdjoint (P n)
  /-- Each term has finite rank. -/
  finiteRank : ∀ n,
    FiniteDimensional ℂ (LinearMap.range ((P n : H →ₗ[ℂ] H)))
  /-- Asymptotic commutation with the image. -/
  commute_lim : ∀ a : A,
    Tendsto (fun n => ‖P n * π a - π a * P n‖) atTop (nhds 0)
  /-- Strong convergence to the identity. -/
  approx_id : ∀ v : H, Tendsto (fun n => P n v) atTop (nhds v)

namespace IsQuasidiagonalSequence

variable {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {P : ℕ → H →L[ℂ] H}

/-- The compressions are uniformly bounded by the norms. -/
theorem norm_compression_le (hqd : IsQuasidiagonalSequence π P) (a : A)
    (n : ℕ) :
    ‖P n * π a * P n‖ ≤ ‖π a‖ := by
  have hP : ∀ v : H, ‖P n v‖ ≤ ‖v‖ :=
    norm_apply_le_of_projection (hqd.idem n) (hqd.selfadjoint n)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp]
  calc ‖P n (π a (P n v))‖ ≤ ‖π a (P n v)‖ := hP _
    _ ≤ ‖π a‖ * ‖P n v‖ := (π a).le_opNorm _
    _ ≤ ‖π a‖ * ‖v‖ := by
        exact mul_le_mul_of_nonneg_left (hP v) (norm_nonneg _)

/-- **Asymptotic multiplicativity of the compressions**: the single
commutator identity `PaPbP - P(ab)P = Pa(Pb - bP)P` and the asymptotic
commutation squeeze the defect to zero. -/
theorem compression_asymptotically_multiplicative
    (hqd : IsQuasidiagonalSequence π P) (a b : A) :
    Tendsto (fun n =>
      ‖(P n * π a * P n) * (P n * π b * P n) - P n * π (a * b) * P n‖)
      atTop (nhds 0) := by
  have hkey : ∀ n, (P n * π a * P n) * (P n * π b * P n)
      - P n * π (a * b) * P n
      = (P n * π a) * (P n * π b - π b * P n) * P n := by
    intro n
    have hPP : P n * P n = P n := (hqd.idem n).eq
    have e1 : (P n * π a * P n) * (P n * π b * P n)
        = P n * (π a * (P n * (π b * P n))) := by
      simp only [mul_assoc]
      rw [← mul_assoc (P n) (P n), hPP]
    have e2 : (P n * π a) * (P n * π b - π b * P n) * P n
        = P n * (π a * (P n * (π b * P n)))
          - P n * (π a * (π b * P n)) := by
      rw [mul_sub, sub_mul]
      simp only [mul_assoc]
      rw [hPP]
    have e3 : P n * π (a * b) * P n = P n * (π a * (π b * P n)) := by
      rw [map_mul]
      simp only [mul_assoc]
    rw [e1, e3, e2]
  have hb : ∀ n, ‖(P n * π a * P n) * (P n * π b * P n)
      - P n * π (a * b) * P n‖
      ≤ ‖π a‖ * ‖P n * π b - π b * P n‖ := by
    intro n
    rw [hkey n]
    have hP1 : ∀ v : H, ‖P n v‖ ≤ ‖v‖ :=
      norm_apply_le_of_projection (hqd.idem n) (hqd.selfadjoint n)
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun v => ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    calc ‖P n (π a ((P n * π b - π b * P n) (P n v)))‖
        ≤ ‖π a ((P n * π b - π b * P n) (P n v))‖ := hP1 _
      _ ≤ ‖π a‖ * ‖(P n * π b - π b * P n) (P n v)‖ := (π a).le_opNorm _
      _ ≤ ‖π a‖ * (‖P n * π b - π b * P n‖ * ‖P n v‖) := by
          exact mul_le_mul_of_nonneg_left
            ((P n * π b - π b * P n).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖π a‖ * (‖P n * π b - π b * P n‖ * ‖v‖) := by
          have := hP1 v
          gcongr
      _ = ‖π a‖ * ‖P n * π b - π b * P n‖ * ‖v‖ := by ring
  have hlim : Tendsto (fun n => ‖π a‖ * ‖P n * π b - π b * P n‖) atTop
      (nhds 0) := by
    have h := (hqd.commute_lim b).const_mul ‖π a‖
    simpa using h
  exact squeeze_zero (fun n => norm_nonneg _) hb hlim

/-- **Strong convergence of the compressions to the representation.** -/
theorem tendsto_compression_apply (hqd : IsQuasidiagonalSequence π P)
    (a : A) (v : H) :
    Tendsto (fun n => (P n * π a * P n) v) atTop (nhds (π a v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖(P n * π a * P n) v - π a v‖
      ≤ ‖π a‖ * ‖P n v - v‖ + ‖P n (π a v) - π a v‖ := by
    intro n
    have hP1 : ∀ u : H, ‖P n u‖ ≤ ‖u‖ :=
      norm_apply_le_of_projection (hqd.idem n) (hqd.selfadjoint n)
    have hsplit : (P n * π a * P n) v - π a v
        = P n (π a (P n v - v)) + (P n (π a v) - π a v) := by
      rw [mul_apply_eq_comp, mul_apply_eq_comp,
        map_sub, map_sub]
      abel
    rw [hsplit]
    calc ‖P n (π a (P n v - v)) + (P n (π a v) - π a v)‖
        ≤ ‖P n (π a (P n v - v))‖ + ‖P n (π a v) - π a v‖ :=
          norm_add_le _ _
      _ ≤ ‖π a‖ * ‖P n v - v‖ + ‖P n (π a v) - π a v‖ := by
          have h1 : ‖P n (π a (P n v - v))‖ ≤ ‖π a‖ * ‖P n v - v‖ := by
            calc ‖P n (π a (P n v - v))‖ ≤ ‖π a (P n v - v)‖ := hP1 _
              _ ≤ ‖π a‖ * ‖P n v - v‖ := (π a).le_opNorm _
          linarith
  have h1 : Tendsto (fun n => ‖P n v - v‖) atTop (nhds 0) := by
    have := hqd.approx_id v
    rwa [tendsto_iff_norm_sub_tendsto_zero] at this
  have h2 : Tendsto (fun n => ‖P n (π a v) - π a v‖) atTop (nhds 0) := by
    have := hqd.approx_id (π a v)
    rwa [tendsto_iff_norm_sub_tendsto_zero] at this
  have hlim : Tendsto
      (fun n => ‖π a‖ * ‖P n v - v‖ + ‖P n (π a v) - π a v‖) atTop
      (nhds 0) := by
    have h3 := (h1.const_mul ‖π a‖).add h2
    simpa using h3
  exact squeeze_zero (fun n => norm_nonneg _) hb hlim

/-- **The injectivity engine**: an element whose compressions vanish in norm
is killed by the representation.  With a faithful representation, the
compression sequence therefore separates points, which is exactly the
faithfulness of the corona class of the compressions. -/
theorem eq_zero_of_tendsto_compression_norm
    (hqd : IsQuasidiagonalSequence π P) {a : A}
    (h : Tendsto (fun n => ‖P n * π a * P n‖) atTop (nhds 0)) :
    π a = 0 := by
  ext v
  have h1 : Tendsto (fun n => (P n * π a * P n) v) atTop (nhds (π a v)) :=
    tendsto_compression_apply hqd a v
  have h2 : Tendsto (fun n => (P n * π a * P n) v) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ n, ‖(P n * π a * P n) v‖ ≤ ‖P n * π a * P n‖ * ‖v‖ :=
      fun n => (P n * π a * P n).le_opNorm v
    have hlim : Tendsto (fun n => ‖P n * π a * P n‖ * ‖v‖) atTop
        (nhds 0) := by
      have h3 := h.mul_const ‖v‖
      simpa using h3
    exact squeeze_zero (fun n => norm_nonneg _) hb hlim
  have h4 : π a v = 0 := tendsto_nhds_unique h1 h2
  rw [h4, zero_apply]

/-- The star-compatibility of the compressions: compressing the adjoint is
the adjoint of the compression. -/
theorem compression_star (hqd : IsQuasidiagonalSequence π P) (a : A)
    (n : ℕ) :
    P n * π (star a) * P n = star (P n * π a * P n) := by
  have hP : star (P n) = P n := (hqd.selfadjoint n).star_eq
  rw [star_mul, star_mul, hP, map_star, mul_assoc]

end IsQuasidiagonalSequence

end Quasidiagonal
end GroupApproximation
