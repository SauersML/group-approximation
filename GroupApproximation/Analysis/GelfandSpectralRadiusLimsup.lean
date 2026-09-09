import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import GroupApproximation.Meta.AxiomGuard

/-!
# Gelfand's formula as a real `limsup`

`limsup_norm_pow_rpow_inv_eq_spectralRadius`:

  `limsup_k ‖x^k‖^(1/k) = (spectralRadius ℂ x).toReal`

for `x` in a complex Banach algebra.

## Why this shape

`Manuscript/NonMF/GerasimovaOsinTheorem11Slice` reduces the Gerasimova--Osin
citation to two named inputs, one of which is Dykema--de la Harpe's Theorem 1.4,
and that theorem is about the *spectral radius* of an element of `C*_r(G)`.  The
slice defines the radius by hand,

  `operatorSpectralRadius x = limsup (fun k ↦ ‖x ^ k‖ ^ ((k : ℝ)⁻¹)) atTop`,

a real `limsup` about which nothing was proved, so
`HasL2SpectralRadiusProperty` was a statement about an opaque quantity rather
than about the spectrum.  This module identifies that quantity.

Mathlib's Gelfand formula, `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`,
is a `Tendsto` in `ℝ≥0∞`.  Three steps separate it from the `limsup` above: the
spectral radius of a bounded element is finite, so `ENNReal.toReal` is continuous
there; `toReal` of `ofReal` is the identity on nonnegative reals; and a
convergent sequence has its limit as `limsup`.  None of that is analysis, but
none of it is free either, and doing it once here means the Dykema--de la Harpe
work can quote the spectrum.

## Why it is stated for a Banach algebra rather than for `C*_r(G)`

Deliberately, so that this module depends on no unlanded work.  The
Gerasimova--Osin slice is being written concurrently in another lane and is not
on `origin/main`; importing it here would be a dangling import.  The theorem
below is the whole mathematical content, and when that slice lands,

  `operatorSpectralRadius x = (spectralRadius ℂ x).toReal`

is this theorem with `A := ReducedGroupCStar G`, since the slice's definition is
literally the `limsup` on the left.  Nothing has to be re-proved.
-/

open Filter Topology

namespace GroupApproximation

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [NormOneClass A]

/-- The spectral radius of an element of a complex Banach algebra is finite: it
is bounded by the norm. -/
theorem spectralRadius_ne_top (x : A) : spectralRadius ℂ x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm x)

/-- **Gelfand's formula as a real `limsup`.**

`limsup_k ‖x^k‖^(1/k)` is the spectral radius, read as a real number.  The
sequence converges, so the `limsup` is its limit, and the limit is Mathlib's
`spectralRadius ℂ x` after `ENNReal.toReal`, which is faithful here because the
radius is finite. -/
theorem limsup_norm_pow_rpow_inv_eq_spectralRadius (x : A) :
    limsup (fun k : ℕ ↦ ‖x ^ k‖ ^ ((k : ℝ)⁻¹)) atTop = (spectralRadius ℂ x).toReal := by
  have hT : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (‖x ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ x)) :=
    spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius x
  have hT2 : Tendsto (fun n : ℕ ↦ (ENNReal.ofReal (‖x ^ n‖ ^ (1 / n : ℝ))).toReal) atTop
      (𝓝 (spectralRadius ℂ x).toReal) :=
    (ENNReal.tendsto_toReal (spectralRadius_ne_top x)).comp hT
  have hfun : (fun n : ℕ ↦ (ENNReal.ofReal (‖x ^ n‖ ^ (1 / n : ℝ))).toReal)
      = fun n : ℕ ↦ ‖x ^ n‖ ^ ((n : ℝ)⁻¹) := by
    funext n
    rw [ENNReal.toReal_ofReal (by positivity), one_div]
  rw [hfun] at hT2
  exact hT2.limsup_eq

/-- The same with the `1 / k` spelling. -/
theorem limsup_norm_pow_one_div_eq_spectralRadius (x : A) :
    limsup (fun k : ℕ ↦ ‖x ^ k‖ ^ (1 / k : ℝ)) atTop = (spectralRadius ℂ x).toReal := by
  simpa only [one_div] using limsup_norm_pow_rpow_inv_eq_spectralRadius x

/-- **The sequence converges**, which is what makes the `limsup` above harmless:
any statement proved about the `limsup` is a statement about the limit. -/
theorem tendsto_norm_pow_rpow_inv (x : A) :
    Tendsto (fun k : ℕ ↦ ‖x ^ k‖ ^ ((k : ℝ)⁻¹)) atTop
      (𝓝 (spectralRadius ℂ x).toReal) := by
  have hT : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (‖x ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ x)) :=
    spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius x
  have hT2 : Tendsto (fun n : ℕ ↦ (ENNReal.ofReal (‖x ^ n‖ ^ (1 / n : ℝ))).toReal) atTop
      (𝓝 (spectralRadius ℂ x).toReal) :=
    (ENNReal.tendsto_toReal (spectralRadius_ne_top x)).comp hT
  have hfun : (fun n : ℕ ↦ (ENNReal.ofReal (‖x ^ n‖ ^ (1 / n : ℝ))).toReal)
      = fun n : ℕ ↦ ‖x ^ n‖ ^ ((n : ℝ)⁻¹) := by
    funext n
    rw [ENNReal.toReal_ofReal (by positivity), one_div]
  rwa [hfun] at hT2

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.spectralRadius_ne_top
#audit_axioms GroupApproximation.limsup_norm_pow_rpow_inv_eq_spectralRadius
#audit_axioms GroupApproximation.limsup_norm_pow_one_div_eq_spectralRadius
#audit_axioms GroupApproximation.tendsto_norm_pow_rpow_inv
