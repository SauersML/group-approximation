import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongPivot
import GroupApproximation.BooneHigman.Metabelian.SuslinCongIndStatement
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The monic `SL₂`-block Statement in degree `≤ 1` (no stabilization, no constant term)

Lane `bh-met-93h`.  Target: `suslinCongInd_MonicStab R` (`SuslinCongIndStatement.lean`).
This file proves its degree-`≤ 1` part, in a STRONGER form: if `τ ∈ SL₂(R[X])` and
`f = τ₀₀` has a unit leading coefficient and `deg f ≤ 1`, then `τ ∈ E₂(R[X])` already
(`suslinMonic_mem_of_natDegree_le_one`), hence `diag(τ, 1) ∈ E₃(R[X])`
(`suslinMonic_stab_of_natDegree_le_one`), for EVERY commutative ring `R`, with no
constant-term hypothesis.

**Route.**
* `deg f = 0`: `f = C(lc f)` is a unit; unit pivot (`suslinBase3Cong_mem_of_isUnit`).
* `deg f = 1`: `f = C w · X + C b`, `w ∈ Rˣ`; put `r = -w⁻¹ b`, so `f = C w · (X - C r)` and
  `f(r) = 0`.  Write `g = τ₀₁ = C (g(r)) + (X - C r) s` (`X_sub_C_dvd_sub_C_eval`).  Evaluating
  `det τ = f τ₁₁ - g τ₁₀ = 1` at `r` gives `g(r) · (-τ₁₀(r)) = 1`, so `c = g(r) ∈ Rˣ`.  The column
  move `x₀₁(-C w⁻¹ · s)` turns the `(0,1)` entry into `C c`, a unit of `R[X]`; a second column
  move `x₁₀(c⁻¹ (1 - f))` makes the `(0,0)` entry `1`, and the unit pivot finishes.
No resultant, no locality, no Whitehead lemma.  Truth check: scratch `bh-met-93h/check.py`
(route replayed on 9000 random `τ` with `deg τ₀₀ = 1` over `ZMod 4`, `ZMod 6`, `𝔽₂[ε]/(ε²)`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **Unit `(0,1)` entry in rank two.**  A `2 × 2` matrix of determinant `1` whose `(0,1)` entry
is a unit is elementary, over every commutative ring. -/
theorem suslinMonic_mem_of_isUnit_zero_one {B : Type*} [CommRing B]
    (M : (Matrix (Fin 2) (Fin 2) B)ˣ) (hdet : Matrix.det (M : Matrix (Fin 2) (Fin 2) B) = 1)
    (hb : IsUnit ((M : Matrix (Fin 2) (Fin 2) B) 0 1)) :
    M ∈ elementaryGroup (Fin 2) B := by
  obtain ⟨v, hv⟩ := hb
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  obtain ⟨E, hE⟩ : ∃ E : (Matrix (Fin 2) (Fin 2) B)ˣ, E = elementaryUnit (1 : Fin 2) 0 h10
      (((v⁻¹ : Bˣ) : B) * (1 - (M : Matrix (Fin 2) (Fin 2) B) 0 0)) := ⟨_, rfl⟩
  have hEmem : E ∈ elementaryGroup (Fin 2) B := by
    rw [hE]
    exact elementaryUnit_mem _ _ _ _
  have h00 : ((M * E : (Matrix (Fin 2) (Fin 2) B)ˣ) : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := by
    rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, ← hv, ← mul_assoc,
      Units.mul_inv, one_mul]
    ring
  have hdetE : Matrix.det ((M * E : (Matrix (Fin 2) (Fin 2) B)ˣ) :
      Matrix (Fin 2) (Fin 2) B) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdet, suslin_det_eq_one_of_mem_elementaryGroup hEmem,
      one_mul]
  have hME := suslinBase3Cong_mem_of_isUnit (M * E) hdetE (by rw [h00]; exact isUnit_one)
  have h := mul_mem hME (inv_mem hEmem)
  rwa [mul_inv_cancel_right] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_mem_of_isUnit_zero_one

/-- **Degree `1`.**  If `f = τ₀₀` has natural degree `1` and a unit leading coefficient, then
`τ ∈ SL₂(R[X])` is elementary. -/
theorem suslinMonic_mem_of_natDegree_eq_one {R : Type*} [CommRing R]
    (τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ)
    (hdet : Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1) (f : R[X])
    (hf : (τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0 = f)
    (hlc : IsUnit f.leadingCoeff) (h1 : f.natDegree = 1) :
    τ ∈ elementaryGroup (Fin 2) R[X] := by
  obtain ⟨g, hg⟩ : ∃ g : R[X], (τ : Matrix (Fin 2) (Fin 2) R[X]) 0 1 = g := ⟨_, rfl⟩
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one h1.le
  obtain ⟨w, hw⟩ : IsUnit (f.coeff 1) := by
    have h := hlc
    rwa [Polynomial.leadingCoeff, h1] at h
  obtain ⟨b, hb⟩ : ∃ b : R, f.coeff 0 = b := ⟨_, rfl⟩
  rw [← hw, hb] at hlin
  obtain ⟨r, hr⟩ : ∃ r : R, r = -(((w⁻¹ : Rˣ) : R) * b) := ⟨_, rfl⟩
  have hCw : Polynomial.C (w : R) * Polynomial.C ((w⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hfr : f = Polynomial.C (w : R) * (Polynomial.X - Polynomial.C r) := by
    rw [hlin, hr, map_neg, sub_neg_eq_add, mul_add, map_mul, ← mul_assoc, hCw, one_mul]
  have hfr0 : f.eval r = 0 := by
    rw [hfr]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, mul_zero]
  have hc : IsUnit (g.eval r) := by
    have h := congrArg (Polynomial.eval r) hdet
    rw [Matrix.det_fin_two, hf, hg, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_mul, hfr0, zero_mul, zero_sub, Polynomial.eval_one] at h
    exact IsUnit.of_mul_eq_one (-((τ : Matrix (Fin 2) (Fin 2) R[X]) 1 0).eval r)
      (by rw [mul_neg]; exact h)
  obtain ⟨s, hs⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := r) (p := g)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨E, hE⟩ : ∃ E : (Matrix (Fin 2) (Fin 2) R[X])ˣ, E = elementaryUnit (0 : Fin 2) 1 h01
      (-(Polynomial.C ((w⁻¹ : Rˣ) : R) * s)) := ⟨_, rfl⟩
  have hEmem : E ∈ elementaryGroup (Fin 2) R[X] := by
    rw [hE]
    exact elementaryUnit_mem _ _ _ _
  have hrow : ((τ * E : (Matrix (Fin 2) (Fin 2) R[X])ˣ) : Matrix (Fin 2) (Fin 2) R[X]) 0 1 =
      Polynomial.C (g.eval r) := by
    rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, hf, hg, hfr]
    linear_combination hs - (Polynomial.X - Polynomial.C r) * s * hCw
  have hdetE : Matrix.det ((τ * E : (Matrix (Fin 2) (Fin 2) R[X])ˣ) :
      Matrix (Fin 2) (Fin 2) R[X]) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdet, suslin_det_eq_one_of_mem_elementaryGroup hEmem,
      one_mul]
  have hτE := suslinMonic_mem_of_isUnit_zero_one (τ * E) hdetE
    (by rw [hrow]; exact hc.map Polynomial.C)
  have h := mul_mem hτE (inv_mem hEmem)
  rwa [mul_inv_cancel_right] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_mem_of_natDegree_eq_one

/-- **Degree `≤ 1`.**  If `τ₀₀` has natural degree `≤ 1` and a unit leading coefficient, then
`τ ∈ SL₂(R[X])` is elementary (no constant-term hypothesis, no stabilization). -/
theorem suslinMonic_mem_of_natDegree_le_one {R : Type*} [CommRing R]
    (τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ)
    (hdet : Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1)
    (hlc : IsUnit ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).leadingCoeff)
    (hle : ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).natDegree ≤ 1) :
    τ ∈ elementaryGroup (Fin 2) R[X] := by
  obtain ⟨f, hf⟩ : ∃ f : R[X], (τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0 = f := ⟨_, rfl⟩
  rw [hf] at hlc hle
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · refine suslinBase3Cong_mem_of_isUnit τ hdet ?_
    have hu : IsUnit (f.coeff 0) := by
      have h := hlc
      rwa [Polynomial.leadingCoeff, h0] at h
    rw [hf, Polynomial.eq_C_of_natDegree_eq_zero h0]
    exact hu.map Polynomial.C
  · exact suslinMonic_mem_of_natDegree_eq_one τ hdet f hf hlc h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_mem_of_natDegree_le_one

/-- **The monic Statement in degree `≤ 1`** (stabilized form, no constant-term hypothesis). -/
theorem suslinMonic_stab_of_natDegree_le_one {R : Type*} [CommRing R]
    (τ : (Matrix (Fin 2) (Fin 2) R[X])ˣ)
    (hdet : Matrix.det (τ : Matrix (Fin 2) (Fin 2) R[X]) = 1)
    (hlc : IsUnit ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).leadingCoeff)
    (hle : ((τ : Matrix (Fin 2) (Fin 2) R[X]) 0 0).natDegree ≤ 1) :
    stabilizeUnit (R := R[X]) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) R[X] :=
  (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := R[X])
    ⟨τ, suslinMonic_mem_of_natDegree_le_one τ hdet hlc hle⟩).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_stab_of_natDegree_le_one

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
