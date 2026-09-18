import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongLift
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: the deep-congruence core `SuslinBase3CongPowStab`

Lane `bh-met-91k`.

`SuslinBase3CongPowStab A n`: for every maximal ideal `𝔪` of `A` there is SOME exponent `N`
(chosen by the prover, depending on `𝔪`) such that every `σ ∈ SL_n(A[X])` with `σ(0) = 1` and
`σ ≡ 1 mod 𝔪^N` has `diag(σ_𝔪, 1) ∈ E_{n+1}(A_𝔪[X])`.

* `suslinBase3Cong_core_of_powStab` (**the reduction**, every commutative ring `A`, rank `2`):
  `SuslinBase3CongPowStab A 2 → SuslinBase3CoreStab A 2`.

  **Proof.**  Given `σ ≡ 1 mod 𝔪` take the prover's `N`.  Modulo `𝔪^N` the `(0,0)` entry of `σ`
  is `1 + (nilpotent)`, a unit of `(A/𝔪^N)[X]`, so the unit pivot puts `σ mod 𝔪^N` in
  `E₂((A/𝔪^N)[X])`; lifting gives `ε ∈ E₂(A[X])` normalized with `σ' = ε⁻¹σ ≡ 1 mod 𝔪^N`
  (`suslinBase3Cong_exists_factor`).  Then `diag(σ_𝔪,1) = diag(ε_𝔪,1) · diag(σ'_𝔪,1)`.
* `suslinBase3Cong_powStab_of_core` (**truth transfer**, every `A`, every `n`): the core gives
  `SuslinBase3CongPowStab A n` with `N = 1`.

**LOUD status.**
* Logically, `SuslinBase3CongPowStab A 2 ↔ SuslinBase3CoreStab A 2` for every `A` (the two items
  above), so it is NOT strictly weaker in logical strength over an individual ring.  It is
  strictly smaller in PROOF CONTENT: the `𝔪 / 𝔪^N` layer, i.e. all of `SL₂` over the Artinian
  thickening `(A/𝔪^N)[X]`, is discharged here, and the prover may pick `N` as large as needed
  (for example beyond an Artin–Rees or Krull-intersection bound).
* TRUE for the `SuslinBase3CoreGlobalStatement` families exactly when the core is, by the
  equivalence; the core itself is the (true) K1-regularity of the regular local rings
  `A_𝔪`, `A = 𝔽_p[t₁..t_k]` or `ℤ[1/m][t₁..t_k]` (truth witness in `SuslinBase3CoreEndpoint`).
* The remaining gap is still K1-regularity: `σ ≡ 1 mod 𝔪^N` normalized in `SL₂(A[X])` is
  stably elementary over `A_𝔪[X]`.  Nothing here is a citation; it is not τ-free Vorst
  regularity (it is rank-2-plus-one-stabilization over a single polynomial variable).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The deep-congruence core** at rank `n`: for each maximal `𝔪`, some `N` works for all
normalized `σ ≡ 1 mod 𝔪^N` of determinant `1`. -/
def SuslinBase3CongPowStab (A : Type*) [CommRing A] (n : ℕ) : Prop :=
  ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), ∃ N : ℕ,
    ∀ σ : Matrix.GeneralLinearGroup (Fin n) (Polynomial A),
      Matrix.det (σ : Matrix (Fin n) (Fin n) (Polynomial A)) = 1 →
        elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) σ = 1 →
          elementaryMatrixUnitMap (ι := Fin n)
              (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ = 1 →
            stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
                (elementaryMatrixUnitMap (ι := Fin n)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ) ∈
              elementaryGroup (Fin n ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3CongPowStab

/-- **The reduction**: the deep-congruence core gives the congruence core in rank `2`, for every
commutative ring `A`. -/
theorem suslinBase3Cong_core_of_powStab {A : Type*} [CommRing A]
    (h : SuslinBase3CongPowStab A 2) : SuslinBase3CoreStab A 2 := by
  intro σ hdet h0 𝔪 h𝔪 hπ
  obtain ⟨N, hN⟩ := h 𝔪 h𝔪
  obtain ⟨ε, hε, hε0, hεN⟩ := suslinBase3Cong_exists_factor 𝔪 N σ hdet h0 hπ
  have hdε : Matrix.det ((ε⁻¹ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) = 1 :=
    suslin_det_eq_one_of_mem_elementaryGroup (inv_mem hε)
  have hdet' : Matrix.det ((ε⁻¹ * σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
      Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdε, hdet, one_mul]
  have h0' : elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A))
      (ε⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, hε0, h0, inv_one, one_mul]
  have hcore := hN (ε⁻¹ * σ) hdet' h0' hεN
  have hloc : elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) ε ∈
        elementaryGroup (Fin 2) (Localization.AtPrime 𝔪)[X] :=
    elementaryGroup_map_le (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)))
      (Subgroup.mem_map_of_mem _ hε)
  have hstab : stabilizeUnit (R := (Localization.AtPrime 𝔪)[X]) (κ := Unit)
      (elementaryMatrixUnitMap (ι := Fin 2)
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) ε) ∈
        elementaryGroup (Fin 2 ⊕ Unit) (Localization.AtPrime 𝔪)[X] :=
    (elementaryStabilization (ι := Fin 2) (κ := Unit)
      (R := (Localization.AtPrime 𝔪)[X]) ⟨_, hloc⟩).2
  have hprod := mul_mem hstab hcore
  rwa [← map_mul, ← map_mul, mul_inv_cancel_left] at hprod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_core_of_powStab

/-- Congruence modulo `𝔪^N`, `N ≥ 1`, implies congruence modulo `𝔪`. -/
theorem suslinBase3Cong_mod_of_modPow {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (𝔪 : Ideal A) {N : ℕ} (hN : N ≠ 0) (σ : (Matrix ι ι A[X])ˣ)
    (h : elementaryMatrixUnitMap (ι := ι)
      (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ = 1) :
    elementaryMatrixUnitMap (ι := ι) (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) σ = 1 := by
  have key : elementaryMatrixUnitMap (ι := ι) (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) σ =
      elementaryMatrixUnitMap (ι := ι)
        (Polynomial.mapRingHom (Ideal.Quotient.factor (Ideal.pow_le_self hN)))
        (elementaryMatrixUnitMap (ι := ι)
          (Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))) σ) := by
    apply Units.ext
    ext i j
    change ((σ : Matrix ι ι A[X]) i j).map (Ideal.Quotient.mk 𝔪) =
      (((σ : Matrix ι ι A[X]) i j).map (Ideal.Quotient.mk (𝔪 ^ N))).map
        (Ideal.Quotient.factor (Ideal.pow_le_self hN))
    rw [Polynomial.map_map, Ideal.Quotient.factor_comp_mk]
  rw [key, h, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_mod_of_modPow

/-- **Truth transfer**: the congruence core gives the deep-congruence core (with `N = 1`), for
every `A` and every rank. -/
theorem suslinBase3Cong_powStab_of_core {A : Type*} [CommRing A] {n : ℕ}
    (h : SuslinBase3CoreStab A n) : SuslinBase3CongPowStab A n :=
  fun 𝔪 h𝔪 ↦ ⟨1, fun σ hdet h0 h1 ↦
    h σ hdet h0 𝔪 h𝔪 (suslinBase3Cong_mod_of_modPow 𝔪 one_ne_zero σ h1)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_powStab_of_core

/-- In rank `2` the deep-congruence core and the congruence core are equivalent. -/
theorem suslinBase3Cong_powStab_iff_core {A : Type*} [CommRing A] :
    SuslinBase3CongPowStab A 2 ↔ SuslinBase3CoreStab A 2 :=
  ⟨suslinBase3Cong_core_of_powStab, suslinBase3Cong_powStab_of_core⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Cong_powStab_iff_core

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
