import GroupApproximation.BooneHigman.Metabelian.SuslinR1FinNagata
import GroupApproximation.BooneHigman.Metabelian.SuslinR1FinLocal
import GroupApproximation.BooneHigman.Metabelian.SuslinR1Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# R1, finite form: the coordinate-change Statement

Lane `bh-met-90r`.  `SuslinR1FinCoordLocal A N`: every normalized `τ ∈ SL_N(A[X])` becomes,
after a ring automorphism `φ` of `A[X]` and right multiplication by some `ε ∈ E_N(A[X])`, a
matrix with an entry whose leading coefficient is a UNIT.  This is the global "monic trick"
input of Suslin's argument; it involves no localization and no finiteness.

* `suslinR1Fin_normalized_of_coord`: with `N ≥ 3`, `SL_N(A) ⊆ E_N(A)` and R2, the coordinate
  Statement makes every normalized `τ` elementary (`suslinR1Fin_mem_of_unit_lead` for `φ(τ)`,
  then apply `φ⁻¹`).
* `suslinR1Fin_finiteLocal_of_normalized`: an elementary normalized `τ` satisfies the finite
  form of R1 trivially (take `F = τ_𝔪⁻¹`; the ideal contains the diagonal entry `1`).
* `suslinR1Fin_coord_of_field`: over `K[s_0,…,s_{n-1}]`, `K` a field, the coordinate Statement
  HOLDS, with `ε = 1`: Nagata's automorphism (`suslinR1Fin_nagata`) applied to a nonzero entry.
* `suslinR1Fin_coord_of_normalized`: conversely, elementary normalized matrices satisfy the
  coordinate Statement (`φ = id`, `ε = τ⁻¹`).

**Why a unit, not "monic mod 𝔪".**  A polynomial that is monic modulo a maximal ideal does
NOT give finiteness: over `B = k[y]_(y)`, `1 + yX ≡ 1` mod `y`, but `B[X]/(1 + yX) ≅ k(y)` is
not a finite `B`-module.  Over a local `B`, `B[X]/I` is finite iff `I` contains a polynomial with
unit leading coefficient; that is why the Statement asks for a unit leading coefficient.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The coordinate-change Statement**: for every normalized `τ ∈ SL_N(A[X])` there are a
ring automorphism `φ` of `A[X]`, an elementary `ε` and an entry `(r, t)` of `φ(τ) ε` with unit
leading coefficient. -/
def SuslinR1FinCoordLocal (A : Type*) [CommRing A] (N : ℕ) : Prop :=
  ∀ τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
    Matrix.det (τ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ = 1 →
        ∃ φ : Polynomial A ≃+* Polynomial A, ∃ ε ∈ elementaryGroup (Fin N) (Polynomial A),
          ∃ r t : Fin N,
            IsUnit (((elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom τ * ε :
              Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
                Matrix (Fin N) (Fin N) (Polynomial A)) r t).leadingCoeff

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinR1FinCoordLocal

/-- **The coordinate Statement and R2 make normalized matrices elementary.** -/
theorem suslinR1Fin_normalized_of_coord {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (hA : SpecialLinearInElementary A N) (h2 : SuslinR1StabLocal A N)
    (hc : SuslinR1FinCoordLocal A N) : SuslinMonicNormalizedElementary A N := by
  intro τ hdet h0
  obtain ⟨φ, ε, hε, r, t, hu⟩ := hc τ hdet h0
  have hρ : Matrix.det ((elementaryMatrixUnitMap (ι := Fin N) φ.toRingHom τ :
      Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
        Matrix (Fin N) (Fin N) (Polynomial A)) = 1 := by
    change Matrix.det (φ.toRingHom.mapMatrix (τ : Matrix (Fin N) (Fin N) (Polynomial A))) = 1
    rw [← RingHom.map_det, hdet, map_one]
  have hmem := elementaryGroup_map_le (ι := Fin N) φ.symm.toRingHom
    (Subgroup.mem_map_of_mem _ (suslinR1Fin_mem_of_unit_lead hN hA h2 _ hρ ε hε r t hu))
  have hcomp : φ.symm.toRingHom.comp φ.toRingHom = RingHom.id (Polynomial A) :=
    RingHom.ext fun x ↦ by simp
  rwa [suslinLocalGlobal_map_map, hcomp, suslinLocalGlobal_map_id] at hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_normalized_of_coord

/-- **Elementary normalized matrices satisfy the finite form of R1**, with `F = τ_𝔪⁻¹`. -/
theorem suslinR1Fin_finiteLocal_of_normalized {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (h : SuslinMonicNormalizedElementary A N) : SuslinR1FiniteLocal A N := by
  intro τ hdet h0 𝔪 h𝔪
  have hτ := h τ hdet h0
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨t, ht⟩ := exists_ne (⟨0, by omega⟩ : Fin N)
  refine ⟨(elementaryMatrixUnitMap (ι := Fin N)
    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ)⁻¹,
    inv_mem (elementaryGroup_map_le (ι := Fin N) _ (Subgroup.mem_map_of_mem _ hτ)),
    ⟨0, by omega⟩, t, ?_⟩
  have key : ∀ I : Ideal (Polynomial (Localization.AtPrime 𝔪)), I = ⊤ →
      Module.Finite (Localization.AtPrime 𝔪) (Polynomial (Localization.AtPrime 𝔪) ⧸ I) := by
    intro I hI
    have : Subsingleton (Polynomial (Localization.AtPrime 𝔪) ⧸ I) :=
      Ideal.Quotient.subsingleton_iff.2 hI
    infer_instance
  apply key
  rw [mul_inv_cancel, Units.val_one]
  exact (Ideal.eq_top_iff_one _).2
    (Ideal.subset_span ⟨⟨⟨0, by omega⟩, ht.symm⟩, Matrix.one_apply_eq _⟩)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_finiteLocal_of_normalized

/-- **The coordinate Statement over a polynomial ring over a field** (Nagata, with `ε = 1`). -/
theorem suslinR1Fin_coord_of_field {K : Type*} [Field K] {n N : ℕ} (hN : 0 < N) :
    SuslinR1FinCoordLocal (MvPolynomial (Fin n) K) N := by
  intro τ hdet _
  obtain ⟨r, t, hne⟩ : ∃ r t : Fin N,
      (τ : Matrix (Fin N) (Fin N) (Polynomial (MvPolynomial (Fin n) K))) r t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : (τ : Matrix (Fin N) (Fin N) (Polynomial (MvPolynomial (Fin n) K))) = 0 := by
      ext i j
      exact hcon i j
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    rw [hz, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨φ, hφ⟩ := suslinR1Fin_nagata _ hne
  refine ⟨φ, 1, one_mem _, r, t, ?_⟩
  rw [mul_one]
  exact hφ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_coord_of_field

/-- **The converse**: elementary normalized matrices satisfy the coordinate Statement. -/
theorem suslinR1Fin_coord_of_normalized {A : Type*} [CommRing A] {N : ℕ} (hN : 0 < N)
    (h : SuslinMonicNormalizedElementary A N) : SuslinR1FinCoordLocal A N := by
  intro τ hdet h0
  refine ⟨RingEquiv.refl _, τ⁻¹, inv_mem (h τ hdet h0), ⟨0, hN⟩, ⟨0, hN⟩, ?_⟩
  rw [RingEquiv.toRingHom_refl, suslinLocalGlobal_map_id, mul_inv_cancel, Units.val_one,
    Matrix.one_apply_eq, Polynomial.leadingCoeff_one]
  exact isUnit_one

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_coord_of_normalized

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
