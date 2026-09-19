import GroupApproximation.Sofic.HyperlinearScalar

/-!
# Reconciling the two shapes of "asymptotically in the commutant"

The literal Section-3 transport theorem and the consumers that rows `FN.03`
and `ID.05` ask to rewire onto it do not merely live over different model
families — they also write the same hypothesis in two different shapes, and
switching the consumers over needs both differences closed.

**Squared versus unsquared.**  `KazhdanAsymptoticCommutant.HSSqVanishing` asks
for `hsNormSq ≤ ε`; the manuscript's `NaturalHSCommutatorVanishing`, and hence
`GeneralModelTransport.GeneralHSCommutatorVanishing`, asks for
`√(hsNormSq) ≤ ε`.  The two quantify the same convergence, at `ε` versus `ε²`.

**Commutator versus conjugation defect.**  `IsAsymptoticCommutantOf` measures
`x − u x u*`; the transport theorem measures the commutator `x u − u x`.  For a
unitary `u` these have the *same* normalized Hilbert--Schmidt mass, not merely
comparable ones, because `x − u x u* = (x u − u x) u*` and right multiplication
by a unitary is an isometry for that norm (`hsNormSq_mul_right`).  So this
difference costs nothing at all, which is worth knowing before anyone starts
inserting estimates to bridge it.

Neither bridge touches `Sofic/KazhdanAsymptoticCommutant.lean`, which stays
frozen until the general-model transport module builds green.
-/

namespace GroupApproximation
namespace TransportShapeBridges

open Matrix

/-! ## Squared against unsquared -/

theorem hsNormSq_le_sq_of_sqrt_le (Y : FiniteModel) (A : Matrix Y Y ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : Real.sqrt (hsNormSq Y A) ≤ ε) :
    hsNormSq Y A ≤ ε ^ 2 := by
  have h0 : 0 ≤ hsNormSq Y A := hsNormSq_nonneg Y A
  -- `hε` is passed explicitly rather than left to the context sweep.  The
  -- Positivstellensatz certificate here does not need it -- `0 ≤ ε` already
  -- follows from `0 ≤ √(hsNormSq Y A) ≤ ε` -- so an unreferenced binder would
  -- draw an `unusedVariables` warning, and this library builds under
  -- `-DwarningAsError=true` (`lakefile.toml`), where that is fatal.
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (hsNormSq Y A), hε]

theorem sqrt_hsNormSq_le_of_le_sq (Y : FiniteModel) (A : Matrix Y Y ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : hsNormSq Y A ≤ ε ^ 2) :
    Real.sqrt (hsNormSq Y A) ≤ ε := by
  have hle := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hε] at hle

/-! ## The commutator against the conjugation defect -/

/-- The adjoint of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup' {Y : FiniteModel} {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) : uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  have h := (Matrix.mem_unitaryGroup_iff').mp hu
  rw [Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact h

/-- **The conjugation defect and the commutator carry the same normalized
Hilbert--Schmidt mass.**  `x − u x u* = (x u − u x) u*`, and right
multiplication by a unitary preserves that mass exactly. -/
theorem hsNormSq_conjugation_defect (Y : FiniteModel) {u : Matrix Y Y ℂ}
    (hu : u ∈ Matrix.unitaryGroup Y ℂ) (x : Matrix Y Y ℂ) :
    hsNormSq Y (x - u * x * uᴴ) = hsNormSq Y (x * u - u * x) := by
  have huu : u * uᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have hfactor : (x * u - u * x) * uᴴ = x - u * x * uᴴ := by
    rw [sub_mul]
    congr 1
    rw [mul_assoc, huu, mul_one]
  rw [← hfactor, hsNormSq_mul_right Y (conjTranspose_mem_unitaryGroup' hu)]

end TransportShapeBridges
end GroupApproximation
