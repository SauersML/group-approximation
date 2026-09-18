import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CoreStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongPivot
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2, congruence core: peeling off the `𝔪 / 𝔪^N` layer

Lane `bh-met-91k`.

* `suslinBase3Cong_lift`: `suslinBase3Core_lift` with the hypothesis `SL_n(K[X]) = E_n(K[X])`
  replaced by the single membership `π σ ∈ E_n(K[X])` that its proof uses.
* `suslinBase3Cong_isUnit_diag`: if `σ ≡ 1 mod 𝔪` then every diagonal entry of `σ mod 𝔪^N` is a
  unit of `(A/𝔪^N)[X]`.  The entry is `1 + ḡ` where `g = σᵢᵢ - 1` has coefficients in `𝔪`; each
  coefficient of `ḡ` has `N`-th power in `𝔪^N / 𝔪^N = 0`, so `ḡ` is nilpotent.
* `suslinBase3Cong_exists_factor`: for `σ` normalized, of determinant `1` and `≡ 1 mod 𝔪` in
  rank two, and every `N`, there is a normalized `ε ∈ E₂(A[X])` with `ε⁻¹ σ ≡ 1 mod 𝔪^N`.
  Indeed `σ mod 𝔪^N ∈ E₂((A/𝔪^N)[X])` by the unit pivot (`suslinBase3Cong_mem_of_isUnit`), and
  it lifts.  No maximality of `𝔪` is used.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **Lifting one elementary factorization**, normalized at `X = 0`. -/
theorem suslinBase3Cong_lift {A K : Type*} [CommRing A] [CommRing K] (π : A →+* K)
    (hπ : Function.Surjective π) {n : ℕ} (σ : Matrix.GeneralLinearGroup (Fin n) A[X])
    (h0 : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) σ = 1)
    (hK : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) σ ∈
      elementaryGroup (Fin n) K[X]) :
    ∃ ε ∈ elementaryGroup (Fin n) A[X],
      elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) ε = 1 ∧
        elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) ε =
          elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) σ := by
  have hmem : elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π) σ ∈
      (elementaryGroup (Fin n) A[X]).map
        (elementaryMatrixUnitMap (ι := Fin n) (Polynomial.mapRingHom π)) := by
    rw [elementaryGroup_map_eq_of_surjective (Polynomial.mapRingHom π)
      (by rw [Polynomial.coe_mapRingHom]; exact Polynomial.map_surjective π hπ)]
    exact hK
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

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_lift

/-- **Diagonal entries are units modulo `𝔪^N`** when `σ ≡ 1 mod 𝔪`. -/
theorem suslinBase3Cong_isUnit_diag {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (𝔪 : Ideal A) (N : ℕ) (σ : (Matrix ι ι A[X])ˣ)
    (h𝔪 : elementaryMatrixUnitMap (ι := ι) (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) σ = 1)
    (i : ι) :
    IsUnit (((elementaryMatrixUnitMap (ι := ι)
      (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ :
        (Matrix ι ι (A ⧸ 𝔪 ^ N)[X])ˣ) : Matrix ι ι (A ⧸ 𝔪 ^ N)[X]) i i) := by
  have hent : ((σ : Matrix ι ι A[X]) i i).map (Ideal.Quotient.mk 𝔪) = 1 := by
    have h := congrArg (fun g : (Matrix ι ι (A ⧸ 𝔪)[X])ˣ ↦ (g : Matrix ι ι (A ⧸ 𝔪)[X]) i i) h𝔪
    change Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪) ((σ : Matrix ι ι A[X]) i i) =
      ((1 : (Matrix ι ι (A ⧸ 𝔪)[X])ˣ) : Matrix ι ι (A ⧸ 𝔪)[X]) i i at h
    rw [Units.val_one, Matrix.one_apply_eq, Polynomial.coe_mapRingHom] at h
    exact h
  have hcoef : ∀ k : ℕ, ((σ : Matrix ι ι A[X]) i i - 1).coeff k ∈ 𝔪 := by
    intro k
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map (Ideal.Quotient.mk 𝔪),
      Polynomial.map_sub, hent, Polynomial.map_one, sub_self, Polynomial.coeff_zero]
  have hnil : IsNilpotent (((σ : Matrix ι ι A[X]) i i - 1).map (Ideal.Quotient.mk (𝔪 ^ N))) := by
    refine Polynomial.isNilpotent_iff.mpr fun k ↦ ?_
    rw [Polynomial.coeff_map]
    refine ⟨N, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (hcoef k) N
  have hu := hnil.isUnit_one_add
  have hsum : (1 : (A ⧸ 𝔪 ^ N)[X]) +
      (((σ : Matrix ι ι A[X]) i i - 1).map (Ideal.Quotient.mk (𝔪 ^ N))) =
        ((σ : Matrix ι ι A[X]) i i).map (Ideal.Quotient.mk (𝔪 ^ N)) := by
    rw [Polynomial.map_sub, Polynomial.map_one]
    ring
  rw [hsum] at hu
  change IsUnit (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N)) ((σ : Matrix ι ι A[X]) i i))
  rw [Polynomial.coe_mapRingHom]
  exact hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_isUnit_diag

/-- **Peeling off `𝔪 / 𝔪^N` in rank two.**  A normalized `σ ∈ SL₂(A[X])` with `σ ≡ 1 mod 𝔪` is
`ε · σ'` with `ε ∈ E₂(A[X])` normalized and `σ' = ε⁻¹ σ ≡ 1 mod 𝔪^N`, for every ideal `𝔪` and
every `N`. -/
theorem suslinBase3Cong_exists_factor {A : Type*} [CommRing A] (𝔪 : Ideal A) (N : ℕ)
    (σ : Matrix.GeneralLinearGroup (Fin 2) A[X])
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1)
    (h0 : elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A)) σ = 1)
    (h𝔪 : elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) σ = 1) :
    ∃ ε ∈ elementaryGroup (Fin 2) A[X],
      elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A)) ε = 1 ∧
        elementaryMatrixUnitMap (ι := Fin 2)
          (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) (ε⁻¹ * σ) = 1 := by
  have hdet' : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ :
        (Matrix (Fin 2) (Fin 2) (A ⧸ 𝔪 ^ N)[X])ˣ) : Matrix (Fin 2) (Fin 2) (A ⧸ 𝔪 ^ N)[X]) = 1 := by
    change Matrix.det ((Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))).mapMatrix
      (σ : Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hdet, map_one]
  have hK := suslinBase3Cong_mem_of_isUnit _ hdet' (suslinBase3Cong_isUnit_diag 𝔪 N σ h𝔪 0)
  obtain ⟨ε, hε, hε0, hεπ⟩ :=
    suslinBase3Cong_lift (Ideal.Quotient.mk (𝔪 ^ N)) Ideal.Quotient.mk_surjective σ h0 hK
  refine ⟨ε, hε, hε0, ?_⟩
  rw [map_mul, map_inv, inv_mul_eq_one]
  exact hεπ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_exists_factor

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
