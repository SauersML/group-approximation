import GroupApproximation.BooneHigman.Metabelian.SuslinCongIndStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3FamLift
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalCompose
import GroupApproximation.Meta.AxiomGuard

/-!
# The monic `SL₂`-block Statement plus a Nagata property gives `SL₂(A[X]) ⊆ E₃(A[X])`

Lane `bh-met-93c`.  For a nontrivial commutative ring `A` with
* the **Nagata property** (every nonzero `g ∈ A[X]` has unit leading coefficient after some ring
  automorphism of `A[X]`; proved for `A = K[s_0,…,s_{n-1}]`, `K` a field, in
  `suslinR1Fin_nagata`), and
* `SL₃(A) = E₃(A)` (the family hypothesis of the BH chain at level `k`, NOT at `k + 1`),

the monic `SL₂`-block Statement `suslinCongInd_MonicStab A` gives `diag(σ, 1) ∈ E₃(A[X])` for
EVERY `σ ∈ SL₂(A[X])` (`suslinCongInd_stab_mem_of_nagata`), hence
`SuslinBase3StabLocal A 2` (`suslinCongInd_stabLocal_of_nagata`).

**Route (the `SL₂` block is kept whole throughout).**
1. `e ∈ E₂(A[X])` with `(e σ)₀₀ = σ₀₀ + σ₁₀ ≠ 0` (if `σ₀₀ = 0` then `det σ = 1` forces
   `σ₁₀ ≠ 0`); `diag(e, 1) ∈ E₃` by `elementaryStabilization`.
2. Nagata `φ` makes the leading coefficient of `φ((e σ)₀₀)` a unit.
3. `ρ = φ(e σ) ∈ SL₂(A[X])`; `diag(ρ(0), 1) ∈ E₃(A)` from `SL₃(A) = E₃(A)`
   (`suslinBase3Fam_stab_mem`); the monic Statement gives `diag(ρ, 1) ∈ E₃(A[X])`.
4. Pull back along `φ⁻¹` (`elementaryGroup_map_le`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- An elementary `e ∈ E₂(B)` with `(e σ)₀₀ = σ₀₀ + σ₁₀`. -/
theorem suslinCongInd_exists_elem_entry {B : Type*} [CommRing B]
    (σ : (Matrix (Fin 2) (Fin 2) B)ˣ) :
    ∃ e ∈ elementaryGroup (Fin 2) B,
      ((e * σ : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) 0 0 =
        (σ : Matrix (Fin 2) (Fin 2) B) 0 0 + (σ : Matrix (Fin 2) (Fin 2) B) 1 0 := by
  refine ⟨elementaryUnit (0 : Fin 2) 1 (by decide) 1, elementaryUnit_mem _ _ _ _, ?_⟩
  change ((1 + Matrix.single (0 : Fin 2) 1 (1 : B)) * (σ : Matrix (Fin 2) (Fin 2) B)) 0 0 = _
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.single_mul_apply_same, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_exists_elem_entry

/-- **Pull-back along a ring automorphism**: if `diag(φ τ, 1)` is elementary then so is
`diag(τ, 1)`. -/
theorem suslinCongInd_stab_of_map_equiv {B : Type*} [CommRing B] (φ : B ≃+* B)
    (τ : (Matrix (Fin 2) (Fin 2) B)ˣ)
    (h : stabilizeUnit (R := B) (κ := Unit) (elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom τ) ∈
      elementaryGroup (Fin 2 ⊕ Unit) B) :
    stabilizeUnit (R := B) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) B := by
  have hcomp : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id B :=
    RingHom.ext fun x ↦ by simp
  have hτ : τ = elementaryMatrixUnitMap (ι := Fin 2) φ.symm.toRingHom
      (elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom τ) := by
    rw [suslinLocalGlobal_map_map, hcomp, suslinLocalGlobal_map_id]
  rw [hτ, ← suslinBase3_map_stabilize (κ := Unit)]
  exact elementaryGroup_map_le φ.symm.toRingHom (Subgroup.mem_map_of_mem _ h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stab_of_map_equiv

/-- **Step 2–4**: for `τ ∈ SL₂(A[X])` with `τ₀₀ ≠ 0`, Nagata plus the monic Statement plus
`SL₃(A) = E₃(A)` give `diag(τ, 1) ∈ E₃(A[X])`. -/
theorem suslinCongInd_stab_of_ne_zero {A : Type*} [CommRing A]
    (hN : ∀ g : A[X], g ≠ 0 → ∃ φ : A[X] ≃+* A[X], IsUnit (φ g).leadingCoeff)
    (hSL : SpecialLinearInElementary A 3) (hM : suslinCongInd_MonicStab A)
    (τ : (Matrix (Fin 2) (Fin 2) A[X])ˣ)
    (hdet : Matrix.det (τ : Matrix (Fin 2) (Fin 2) A[X]) = 1)
    (h0 : (τ : Matrix (Fin 2) (Fin 2) A[X]) 0 0 ≠ 0) :
    stabilizeUnit (R := A[X]) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] := by
  obtain ⟨φ, hφ⟩ := hN _ h0
  refine suslinCongInd_stab_of_map_equiv φ τ ?_
  have hρ : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom τ :
      (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
    change Matrix.det (φ.toRingHom.mapMatrix (τ : Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hdet, map_one]
  have hlead : IsUnit (((elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom τ :
      (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Matrix (Fin 2) (Fin 2) A[X]) 0 0).leadingCoeff := hφ
  have hc : Matrix.det ((elementaryMatrixUnitMap (ι := Fin 2) (Polynomial.constantCoeff (R := A))
      (elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom τ) : (Matrix (Fin 2) (Fin 2) A)ˣ) :
        Matrix (Fin 2) (Fin 2) A) = 1 := by
    change Matrix.det ((Polynomial.constantCoeff (R := A)).mapMatrix
      ((elementaryMatrixUnitMap (ι := Fin 2) φ.toRingHom τ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
        Matrix (Fin 2) (Fin 2) A[X])) = 1
    rw [← RingHom.map_det, hρ, map_one]
  exact hM _ hρ hlead (suslinBase3Fam_stab_mem (n := 2) hSL _ hc)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stab_of_ne_zero

/-- **Every `σ ∈ SL₂(A[X])` is stably elementary**, for a nontrivial `A` with the Nagata property
and `SL₃(A) = E₃(A)`, from the monic `SL₂`-block Statement. -/
theorem suslinCongInd_stab_mem_of_nagata {A : Type*} [CommRing A] [Nontrivial A]
    (hN : ∀ g : A[X], g ≠ 0 → ∃ φ : A[X] ≃+* A[X], IsUnit (φ g).leadingCoeff)
    (hSL : SpecialLinearInElementary A 3) (hM : suslinCongInd_MonicStab A)
    (σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1) :
    stabilizeUnit (R := A[X]) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X] := by
  by_cases h00 : (σ : Matrix (Fin 2) (Fin 2) A[X]) 0 0 = 0
  · have h10 : (σ : Matrix (Fin 2) (Fin 2) A[X]) 1 0 ≠ 0 := by
      intro h10
      have h := hdet
      rw [Matrix.det_fin_two, h00, h10, zero_mul, mul_zero, sub_zero] at h
      exact zero_ne_one h
    obtain ⟨e, he, hentry⟩ := suslinCongInd_exists_elem_entry σ
    have hdet' : Matrix.det ((e * σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) :
        Matrix (Fin 2) (Fin 2) A[X]) = 1 := by
      rw [Units.val_mul, Matrix.det_mul, suslin_det_eq_one_of_mem_elementaryGroup he, hdet,
        one_mul]
    have h0' : ((e * σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ) : Matrix (Fin 2) (Fin 2) A[X]) 0 0 ≠
        0 := by
      rw [hentry, h00, zero_add]
      exact h10
    have hstab : stabilizeUnit (R := A[X]) (κ := Unit) e⁻¹ ∈
        elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
      (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := A[X]) ⟨e⁻¹, inv_mem he⟩).2
    rw [← inv_mul_cancel_left e σ, map_mul]
    exact mul_mem hstab (suslinCongInd_stab_of_ne_zero hN hSL hM _ hdet' h0')
  · exact suslinCongInd_stab_of_ne_zero hN hSL hM σ hdet h00

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stab_mem_of_nagata

/-- A GLOBAL stable-elementarity statement for `SL₂(A[X])` gives the localized residual. -/
theorem suslinCongInd_stabLocal_of_global {A : Type*} [CommRing A]
    (h : ∀ σ : (Matrix (Fin 2) (Fin 2) A[X])ˣ, Matrix.det (σ : Matrix (Fin 2) (Fin 2) A[X]) = 1 →
      stabilizeUnit (R := A[X]) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) A[X]) :
    SuslinBase3StabLocal A 2 := by
  intro σ hdet _ 𝔪 _
  rw [← suslinBase3_map_stabilize (κ := Unit)]
  exact elementaryGroup_map_le (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)))
    (Subgroup.mem_map_of_mem _ (h σ hdet))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stabLocal_of_global

/-- **The residual at one ring**: Nagata, `SL₃(A) = E₃(A)` and the monic Statement give
`SuslinBase3StabLocal A 2`. -/
theorem suslinCongInd_stabLocal_of_nagata {A : Type*} [CommRing A] [Nontrivial A]
    (hN : ∀ g : A[X], g ≠ 0 → ∃ φ : A[X] ≃+* A[X], IsUnit (φ g).leadingCoeff)
    (hSL : SpecialLinearInElementary A 3) (hM : suslinCongInd_MonicStab A) :
    SuslinBase3StabLocal A 2 :=
  suslinCongInd_stabLocal_of_global (suslinCongInd_stab_mem_of_nagata hN hSL hM)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongInd_stabLocal_of_nagata

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
