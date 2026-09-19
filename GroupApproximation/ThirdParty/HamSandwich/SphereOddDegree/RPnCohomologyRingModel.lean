import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Apache-2.0 source ported from `akopjan/HamSandwich` commit
`76202dbbb6610ffcebbccfbf7a56f833a4c2a376`.

Porting changes for Mathlib v4.32:

* make `RPnCohomologyRingModel` an abbreviation so the quotient's canonical
  ring and algebra instances remain definitionally aligned;
* replace the deprecated `push_neg` spelling by `push Not`.
-/

open Polynomial

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The algebraic model `F₂[α] / (αⁿ⁺¹)` for the mod-two cohomology ring
of real projective `n`-space. -/
noncomputable abbrev RPnCohomologyRingModel (n : ℕ) : Type :=
  (ZMod 2)[X] ⧸ (Ideal.span {(X : (ZMod 2)[X]) ^ (n + 1)})

/-- The residue class of the polynomial generator. -/
noncomputable def modelAlpha (n : ℕ) : RPnCohomologyRingModel n :=
  Ideal.Quotient.mk _ X

/-- A power of the model generator vanishes exactly at the truncation bound. -/
theorem modelAlpha_pow_eq_zero_iff (n k : ℕ) :
    (modelAlpha n) ^ k = 0 ↔ n + 1 ≤ k := by
  unfold modelAlpha RPnCohomologyRingModel
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [Polynomial.X_pow_dvd_iff] at h
    have := h k (by omega)
    rw [Polynomial.coeff_X_pow, if_pos rfl] at this
    exact one_ne_zero this
  · intro h
    exact pow_dvd_pow X h

/-- The defining truncation relation. -/
@[simp] theorem modelAlpha_pow_succ_eq_zero (n : ℕ) :
    (modelAlpha n) ^ (n + 1) = 0 := by
  rw [modelAlpha_pow_eq_zero_iff]

/-- Powers strictly below the truncation bound are nonzero. -/
theorem modelAlpha_pow_ne_zero (n k : ℕ) (hk : k ≤ n) :
    (modelAlpha n) ^ k ≠ 0 := by
  rw [Ne, modelAlpha_pow_eq_zero_iff]
  omega

/-- The top power survives. -/
theorem modelAlpha_pow_top_ne_zero (n : ℕ) :
    (modelAlpha n) ^ n ≠ 0 :=
  modelAlpha_pow_ne_zero n n le_rfl

/-- The model generator is nilpotent. -/
theorem modelAlpha_isNilpotent (n : ℕ) : IsNilpotent (modelAlpha n) :=
  ⟨n + 1, modelAlpha_pow_succ_eq_zero n⟩

/-- The model has total `F₂`-dimension `n + 1`. -/
theorem modelAlpha_finrank (n : ℕ) :
    Module.finrank (ZMod 2) (RPnCohomologyRingModel n) = n + 1 := by
  have hmonic : (((X : (ZMod 2)[X]) ^ (n + 1))).Monic := monic_X_pow _
  have h := (AdjoinRoot.powerBasis' hmonic).finrank
  rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow] at h
  exact h

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
