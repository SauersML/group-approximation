import Mathlib

/-!
# A punctured normed space is homotopy equivalent to its unit sphere

Model-independent input for the Mayer–Vietoris computation of `H^*(ℂP^n; ℤ)`. Nothing
here mentions projective space; it is kept in its own module precisely so that it can be
compiled without the LIX projection model.

* `AlgTop.puncturedHomotopyEquivSphere E : ↥({0}ᶜ : Set E) ≃ₕ ↥(sphere (0:E) 1)` for any
  real normed space `E`. Route: Mathlib's polar-coordinate homeomorphism
  `homeomorphUnitSphereProd E : ↥({0}ᶜ) ≃ₜ sphere (0:E) 1 × Ioi (0:ℝ)`, then kill the
  radial factor, which is convex and nonempty, hence contractible.
* `AlgTop.complexToEuclidean n : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2*n))`,
  obtained from a dimension count alone — no real basis of `ℂ^n` is written down.
* `AlgTop.complexPuncturedHomotopyEquivSphere d :
    {w : Fin (d+1) → ℂ // w ≠ 0} ≃ₕ ↥(sphere (0 : EuclideanSpace ℝ (Fin (2*(d+1)))) 1)`,
  i.e. `ℂ^{d+1} ∖ {0} ≃ S^{2d+1}`.
-/

noncomputable section

namespace GroupApproximation.AlgTop

/-! ## 1. A punctured normed space and its unit sphere -/

theorem contractibleSpace_Ioi_zero : ContractibleSpace ↥(Set.Ioi (0 : ℝ)) :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩

/-- **In any real normed space the complement of the origin is homotopy equivalent to the
unit sphere.** Polar coordinates plus contractibility of the radial factor. -/
def puncturedHomotopyEquivSphere (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv ↥({0}ᶜ : Set E) ↥(Metric.sphere (0 : E) 1) := by
  haveI := contractibleSpace_Ioi_zero
  refine ((homeomorphUnitSphereProd E).toHomotopyEquiv).trans ?_
  refine (ContinuousMap.HomotopyEquiv.prodCongr
    (ContinuousMap.HomotopyEquiv.refl ↥(Metric.sphere (0 : E) 1))
    (ContractibleSpace.hequiv_unit ↥(Set.Ioi (0 : ℝ))).some).trans ?_
  exact (Homeomorph.prodUnique ↥(Metric.sphere (0 : E) 1) Unit).toHomotopyEquiv

/-! ## 2. `ℂ^n` is `ℝ^{2n}` -/

theorem finrank_pi_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype ℝ]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

theorem finrank_eq_euclidean (n : ℕ) :
    Module.finrank ℝ (Fin n → ℂ)
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
  rw [finrank_pi_complex n, finrank_euclideanSpace_fin]

/-- A real-linear homeomorphism `ℂ^n ≃ ℝ^{2n}`, by a dimension count. -/
def complexToEuclidean (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_eq_euclidean n)

theorem complexToEuclidean_eq_zero_iff (n : ℕ) (w : Fin n → ℂ) :
    complexToEuclidean n w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h1 := congrArg (complexToEuclidean n).symm h
    simpa using h1
  · rintro rfl
    simp

/-- The punctured `ℂ^n` is homeomorphic to the punctured `ℝ^{2n}`. -/
def complexPuncturedHomeo (n : ℕ) :
    {w : Fin n → ℂ // w ≠ 0} ≃ₜ ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin (2 * n)))) :=
  (complexToEuclidean n).toHomeomorph.subtype
    (p := fun w : Fin n → ℂ => w ≠ 0)
    (q := fun v : EuclideanSpace ℝ (Fin (2 * n)) => v ∈ ({0}ᶜ : Set _))
    (fun w => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact not_congr (complexToEuclidean_eq_zero_iff n w).symm)

/-- **`ℂ^{d+1} ∖ {0}` is homotopy equivalent to `S^{2d+1}`.** -/
def complexPuncturedHomotopyEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv {w : Fin (d + 1) → ℂ // w ≠ 0}
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1) :=
  ((complexPuncturedHomeo (d + 1)).toHomotopyEquiv).trans
    (puncturedHomotopyEquivSphere (EuclideanSpace ℝ (Fin (2 * (d + 1)))))

end GroupApproximation.AlgTop
