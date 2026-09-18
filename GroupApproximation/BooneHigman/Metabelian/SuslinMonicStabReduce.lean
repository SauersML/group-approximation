import GroupApproximation.BooneHigman.Metabelian.SuslinMonicStabLinear
import GroupApproximation.Meta.AxiomGuard

/-!
# Reducing the monic Statement to degree `≥ 2` with a reduced `(0,1)` entry

Lane `bh-met-93h`.  `suslinCongInd_MonicStab R` is reduced to `suslinMonic_StabHigh R`: the same
Statement restricted to `2 ≤ deg τ₀₀` and `deg τ₀₁ < deg τ₀₀`
(`suslinMonic_monicStab_of_high`).  Proof: degree `≤ 1` is closed outright
(`suslinMonic_stab_of_natDegree_le_one`); otherwise, with `u = lc τ₀₀` and the monic
`F = C u⁻¹ · τ₀₀`, the column move `x₀₁(-C u⁻¹ · (τ₀₁ /ₘ F))` replaces `τ₀₁` by `τ₀₁ %ₘ F`, keeps
`τ₀₀`, keeps `det = 1`, and keeps the constant-term hypothesis (it multiplies the constant term
by an elementary matrix).

**LOUD honesty notes.**
* `suslinMonic_StabHigh R` is a TRUE special case of Suslin's monic theorem, and it is
  LOGICALLY EQUIVALENT to `suslinCongInd_MonicStab R` (the converse is trivial: drop the two
  degree hypotheses).  It is strictly smaller only in PROOF CONTENT: the degree-`≤ 1` case and
  the Euclid normalisation are discharged here.  It still carries the essential
  `K₁`-Horrocks content (Suslin's monic theorem proper, which needs local-global patching in
  general); nothing in this lane closes it.
* The row version (fallback (a)) was NOT taken: for `τ ∈ SL₂`, the stabilized first row
  `(f, g, 0)` always reaches `e₁` by elementary moves (`(f,g,0) → (f,g,1) → (0,0,1) → e₁`), so it
  is vacuous and gives no information about `diag(τ, 1)`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The monic Statement restricted to `2 ≤ deg τ₀₀` and `deg τ₀₁ < deg τ₀₀`.  TRUE (special case
of Suslin); logically equivalent to `suslinCongInd_MonicStab R`, smaller in proof content. -/
def suslinMonic_StabHigh (R : Type*) [CommRing R] : Prop :=
  ∀ τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ, Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1 →
    IsUnit ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).leadingCoeff →
    2 ≤ ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).natDegree →
    ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 1).natDegree <
      ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).natDegree →
    stabilizeUnit (R := R) (κ := Unit) (elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.constantCoeff (R := R)) τ) ∈ elementaryGroup (Fin 2 ⊕ Unit) R →
    stabilizeUnit (R := R[X]) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) R[X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_StabHigh

/-- **Reduction.**  The high-degree reduced case implies the full monic Statement. -/
theorem suslinMonic_monicStab_of_high {R : Type*} [CommRing R] (hH : suslinMonic_StabHigh R) :
    suslinCongInd_MonicStab R := by
  intro τ hdet hlc hconst
  by_cases hle : ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).natDegree ≤ 1
  · exact suslinMonic_stab_of_natDegree_le_one τ hdet hlc hle
  push Not at hle
  obtain ⟨f, hf⟩ : ∃ f : R[X], (τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0 = f := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : R[X], (τ : Matrix (Fin 2) (Fin 2) R[X]) 0 1 = g := ⟨_, rfl⟩
  rw [hf] at hlc hle
  obtain ⟨u, hu⟩ := hlc
  obtain ⟨F, hF⟩ : ∃ F : R[X], F = Polynomial.C ((u⁻¹ : Rˣ) : R) * f := ⟨_, rfl⟩
  have hFm : F.Monic := by
    rw [hF]
    exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu, Units.inv_mul])
  have hFdeg : F.natDegree = f.natDegree := by
    rw [hF]
    exact Polynomial.natDegree_C_mul_of_isUnit (Units.isUnit _) f
  have hF1 : F ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hFdeg
    omega
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨E, hE⟩ : ∃ E : (Matrix (Fin 2) (Fin 2) R[X])ˣ, E = elementaryUnit (0 : Fin 2) 1 h01
      (-(Polynomial.C ((u⁻¹ : Rˣ) : R) * (g /ₘ F))) := ⟨_, rfl⟩
  have hEmem : E ∈ elementaryGroup (Fin 2) R[X] := by
    rw [hE]
    exact elementaryUnit_mem _ _ _ _
  have hdetE : Matrix.det ((τ * E : (Matrix (Fin 2) (Fin 2) R[X])ˣ) :
      Matrix (Fin 2) (Fin 2) R[X]) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdet, suslin_det_eq_one_of_mem_elementaryGroup hEmem,
      one_mul]
  have h00 : ((τ * E : (Matrix (Fin 2) (Fin 2) R[X])ˣ) : Matrix (Fin 2) (Fin 2) R[X]) 0 0 = f := by
    rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_neg h01, hf]
  have hrow : ((τ * E : (Matrix (Fin 2) (Fin 2) R[X])ˣ) : Matrix (Fin 2) (Fin 2) R[X]) 0 1 =
      g %ₘ F := by
    rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, hf, hg]
    have hmd := Polynomial.modByMonic_add_div g F
    linear_combination -hmd + (g /ₘ F) * hF
  have hconstE : stabilizeUnit (R := R) (κ := Unit) (elementaryMatrixUnitMap (ι := Fin 2)
      (Polynomial.constantCoeff (R := R)) (τ * E)) ∈ elementaryGroup (Fin 2 ⊕ Unit) R := by
    rw [map_mul, map_mul]
    refine mul_mem hconst ?_
    rw [hE, elementaryMatrixUnitMap_elementaryUnit, stabilizeUnit_elementaryUnit]
    exact elementaryUnit_mem _ _ _ _
  have hstab := hH (τ * E) hdetE (by rw [h00]; exact ⟨u, hu⟩) (by rw [h00]; omega)
    (by rw [h00, hrow, ← hFdeg]; exact Polynomial.natDegree_modByMonic_lt g hFm hF1) hconstE
  have hEstab : stabilizeUnit (R := R[X]) (κ := Unit) E ∈ elementaryGroup (Fin 2 ⊕ Unit) R[X] :=
    (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := R[X]) ⟨E, hEmem⟩).2
  have h := mul_mem hstab (inv_mem hEstab)
  rwa [map_mul, mul_inv_cancel_right] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_monicStab_of_high

/-- **Endpoint.**  The high-degree reduced case over every ring gives
`suslinCongInd_MonicStatement`. -/
theorem suslinMonic_monicStatement_of_high
    (h : ∀ (R : Type) [CommRing R], suslinMonic_StabHigh R) :
    suslinCongInd_MonicStatement := by
  intro R _
  exact suslinMonic_monicStab_of_high (h R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_monicStatement_of_high

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
