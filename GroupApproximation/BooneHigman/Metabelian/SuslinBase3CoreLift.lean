import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CoreStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2, congruence core: the residue-field reduction

Lane `bh-met-91h`.

* `suslinBase3Core_lift`: let `π : A → K` be surjective with `SL_n(K[X]) = E_n(K[X])`.  For a
  normalized `σ ∈ SL_n(A[X])` there is a normalized `ε ∈ E_n(A[X])` with `π ε = π σ`.

  **Proof.**  `π σ ∈ SL_n(K[X]) = E_n(K[X])`.  Since `A[X] → K[X]` is surjective, `E_n(A[X])`
  maps onto `E_n(K[X])`, so `π σ = π ε₁` with `ε₁ ∈ E_n(A[X])`.  Put `c₀ = ε₁(0) ∈ E_n(A)` and
  `ε = ε₁ · C(c₀)⁻¹`.  Then `ε(0) = c₀ c₀⁻¹ = 1`, and `π(c₀) = (π ε₁)(0) = (π σ)(0) = π(σ(0)) = 1`,
  so `π ε = π ε₁ = π σ`.

* `suslinBase3Core_stabLocal_of_core`: for `0 < n`, `SuslinBase3CoreStab A n` gives
  `SuslinBase3StabLocal A n`, for EVERY commutative ring `A`.

  **Proof.**  Take `K = A/𝔪`, a field; `SL_n(K[X]) = E_n(K[X])` by the Euclidean algorithm
  (`suslinBase3Core_slField`).  With `ε` as above, `σ' = ε⁻¹ σ` is normalized, of determinant
  `1`, and `≡ 1 mod 𝔪`, so the core gives `diag(σ'_𝔪, 1) ∈ E_{n+1}`.  Also `ε_𝔪 ∈ E_n` and
  `diag(ε_𝔪, 1) ∈ E_{n+1}`.  Hence `diag(σ_𝔪, 1) = diag(ε_𝔪, 1) · diag(σ'_𝔪, 1) ∈ E_{n+1}`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **Lifting a residue-field elementary factorization**, normalized at `X = 0`. -/
theorem suslinBase3Core_lift {A K : Type*} [CommRing A] [CommRing K] (π : A →+* K)
    (hπ : Function.Surjective π) {n : ℕ} (hK : SpecialLinearInElementary K[X] n)
    (σ : Matrix.GeneralLinearGroup (Fin n) A[X])
    (hdet : Matrix.det (σ : Matrix (Fin n) (Fin n) A[X]) = 1)
    (h0 : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) σ = 1) :
    ∃ ε ∈ elementaryGroup (Fin n) A[X],
      elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) ε = 1 ∧
        elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) ε =
          elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) σ := by
  have hdet' : Matrix.det ((elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) σ :
      (Matrix (Fin n) (Fin n) K[X])ˣ) : Matrix (Fin n) (Fin n) K[X]) = 1 := by
    change Matrix.det ((Polynomial.mapRingHom π).mapMatrix
      (σ : Matrix (Fin n) (Fin n) A[X])) = 1
    rw [← RingHom.map_det, hdet, map_one]
  have hmem : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) σ ∈
      (elementaryGroup (Fin n) A[X]).map
        (elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π)) := by
    rw [elementaryGroup_map_eq_of_surjective (Polynomial.mapRingHom π)
      (by rw [Polynomial.coe_mapRingHom]; exact Polynomial.map_surjective π hπ)]
    exact hK _ hdet'
  obtain ⟨ε₁, hε₁, hmap⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, elementaryMatrixUnitMap (ι := Fin n)
      (Polynomial.constantCoeff (R := A)) ε₁ = c₀ := ⟨_, rfl⟩
  have hc₀E : c₀ ∈ elementaryGroup (Fin n) A := by
    rw [← hc₀]
    exact elementaryGroup_map_le (Polynomial.constantCoeff (R := A))
      (Subgroup.mem_map_of_mem _ hε₁)
  have hcE : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.C (R := A)) c₀ ∈
      elementaryGroup (Fin n) A[X] :=
    elementaryGroup_map_le (Polynomial.C (R := A)) (Subgroup.mem_map_of_mem _ hc₀E)
  have hπc₀ : elementaryMatrixUnitMap (ι := Fin n) π c₀ = 1 := by
    rw [← hc₀, suslinBase3Core_map_cc π ε₁, hmap, ← suslinBase3Core_map_cc π σ, h0, map_one]
  refine ⟨ε₁ * (elementaryMatrixUnitMap (ι := Fin n) (Polynomial.C (R := A)) c₀)⁻¹,
    mul_mem hε₁ (inv_mem hcE), ?_, ?_⟩
  · rw [map_mul, map_inv, ← hc₀, suslinBase3Core_cc_C, mul_inv_cancel]
  · rw [map_mul, map_inv, suslinBase3Core_map_C π c₀, hπc₀, map_one, inv_one, mul_one, hmap]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_lift

/-- **The residue-field reduction**: for `0 < n` and every commutative ring `A`, the congruence
core at rank `n` gives the stabilized normalized residual at rank `n`. -/
theorem suslinBase3Core_stabLocal_of_core {A : Type*} [CommRing A] {n : ℕ} (hn : 0 < n)
    (h : SuslinBase3CoreStab A n) : SuslinBase3StabLocal A n := by
  intro σ hdet h0 𝔪 h𝔪
  have hK : SpecialLinearInElementary (Polynomial (A ⧸ 𝔪)) n :=
    @suslinBase3Core_slField (A ⧸ 𝔪) (Ideal.Quotient.field 𝔪) n hn
  obtain ⟨ε, hε, hε0, hεπ⟩ :=
    suslinBase3Core_lift (Ideal.Quotient.mk 𝔪) Ideal.Quotient.mk_surjective hK σ hdet h0
  have hdε : Matrix.det ((ε⁻¹ : (Matrix (Fin n) (Fin n) A[X])ˣ) :
      Matrix (Fin n) (Fin n) A[X]) = 1 :=
    suslin_det_eq_one_of_mem_elementaryGroup (inv_mem hε)
  have hdet' : Matrix.det ((ε⁻¹ * σ : (Matrix (Fin n) (Fin n) A[X])ˣ) :
      Matrix (Fin n) (Fin n) A[X]) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdε, hdet, one_mul]
  have h0' : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A))
      (ε⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, hε0, h0, inv_one, one_mul]
  have hπ' : elementaryMatrixUnitMap (ι := Fin n)
      (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) (ε⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact hεπ
  have hcore := h (ε⁻¹ * σ) hdet' h0' 𝔪 h𝔪 hπ'
  have hloc : elementaryMatrixUnitMap (ι := Fin n)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) ε ∈
        elementaryGroup (Fin n) (Localization.AtPrime 𝔪)[X] :=
    elementaryGroup_map_le (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)))
      (Subgroup.mem_map_of_mem _ hε)
  have hstab : stabilizeUnit (R := (Localization.AtPrime 𝔪)[X]) (κ := Unit)
      (elementaryMatrixUnitMap (ι := Fin n)
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) ε) ∈
        elementaryGroup (Fin n ⊕ Unit) (Localization.AtPrime 𝔪)[X] :=
    (elementaryStabilization (ι := Fin n) (κ := Unit)
      (R := (Localization.AtPrime 𝔪)[X]) ⟨_, hloc⟩).2
  have hprod := mul_mem hstab hcore
  rwa [← map_mul, ← map_mul, mul_inv_cancel_left] at hprod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_stabLocal_of_core

/-- **The converse** (LOUD: the core is a special case), for every `A` and `n`. -/
theorem suslinBase3Core_core_of_stabLocal {A : Type*} [CommRing A] {n : ℕ}
    (h : SuslinBase3StabLocal A n) : SuslinBase3CoreStab A n :=
  fun σ hdet h0 𝔪 h𝔪 _ ↦ h σ hdet h0 𝔪 h𝔪

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_core_of_stabLocal

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
