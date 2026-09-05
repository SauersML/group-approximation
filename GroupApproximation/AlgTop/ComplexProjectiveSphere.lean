import GroupApproximation.AlgTop.ComplexProjectiveCover

/-!
# The intersection of the Mayer–Vietoris cover is a sphere

The last homotopy-theoretic input for `H^*(ℂP^n; ℤ)`. The cover of `ℂP^{d+1}` from
`GroupApproximation/AlgTop/ComplexProjectiveCover.lean` has

```text
chartSet (d+1) ∩ punctured d  ≅  ℂ^{d+1} ∖ {0}  ≃  S^{2d+1}.
```

The first identification is `CPn.chartPuncturedHomeo`. The second is general nonsense
about normed spaces, done here once and for all:

* `CPn.puncturedHomotopyEquivSphere E : ↥({0}ᶜ : Set E) ≃ₕ ↥(sphere (0:E) 1)` for any real
  normed space `E`, via Mathlib's polar-coordinate homeomorphism
  `homeomorphUnitSphereProd E : ↥({0}ᶜ) ≃ₜ sphere (0:E) 1 × Ioi (0:ℝ)` and contractibility
  of `Ioi 0`;
* `CPn.complexPuncturedHomotopyEquivSphere d` transports that along the real-linear
  homeomorphism `ℂ^{d+1} ≃L[ℝ] ℝ^{2d+2}`, which exists because both sides are
  finite-dimensional real spaces of dimension `2d+2`.

## Main results

* `CPn.finrank_pi_complex : Module.finrank ℝ (Fin n → ℂ) = 2 * n`;
* `CPn.puncturedHomotopyEquivSphere`, `CPn.complexPuncturedHomotopyEquivSphere`;
* `CPn.interHomotopyEquivSphere d` — the Mayer–Vietoris intersection is `S^{2d+1}`.

Combined with `CPn.chartHomeo` (the chart is a convex space, hence contractible) and
`CPn.punctureHomotopyEquiv` (the other piece is `ℂP^d`), this pins down every term of the
Mayer–Vietoris sequence for `ℂP^{d+1}` except the sequence itself.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open Matrix
open GroupApproximation.STW59

namespace CPn

/-! ## 1. A punctured normed space is homotopy equivalent to its unit sphere -/

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

/-- A real-linear homeomorphism `ℂ^n ≃ ℝ^{2n}`. -/
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

/-! ## 3. The Mayer–Vietoris intersection -/

/-- **The intersection of the Mayer–Vietoris cover of `ℂP^{d+1}` is homotopy equivalent
to `S^{2d+1}`.** -/
def interHomotopyEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(chartSet (d + 1) ∩ {x : CP (d + 1) | x ≠ basePoint (d + 1)})
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1) :=
  ((chartPuncturedHomeo (d + 1)).symm.toHomotopyEquiv).trans
    (complexPuncturedHomotopyEquivSphere d)

/-- The chart is contractible: it is homeomorphic to a real vector space. -/
theorem contractibleSpace_chartSet (d : ℕ) : ContractibleSpace ↥(chartSet d) :=
  (chartHomeo d).symm.contractibleSpace

end CPn

end GroupApproximation.AlgTop
