import GroupApproximation.BooneHigman.Metabelian.SuslinCongPowMennicke
import GroupApproximation.BooneHigman.Metabelian.SuslinBase3CongPivot
import GroupApproximation.BooneHigman.Metabelian.SuslinCongIndStatement
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# First rows `(f, g)` whose `SL₂`-completions are stably elementary

Lane `bh-met-93i`.  For a commutative ring `S` and `f g : S`, `suslinMonicLocal_Good f g` says:
EVERY `τ ∈ SL₂(S)` with first row `(f, g)` has `diag(τ, 1) ∈ E₃(S)`.  This file proves the
basic closure properties of this predicate over every commutative ring:
* it depends on the first row only (`suslinMonicLocal_stab_of_row`: two `SL₂` matrices with the
  same first row differ by a left `x₂₁(·)`);
* unit entries are good (`suslinMonicLocal_good_of_isUnit`, `…_good_unitRight`);
* column moves (`…_colRight`, `…_colLeft`) and the swap `(f, g) ↦ (g, -f)`.
The Mennicke product rule is in `SuslinMonicLocalMennicke.lean`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Good first rows.**  Every `τ ∈ SL₂(S)` with first row `(f, g)` is stably elementary
(`diag(τ, 1) ∈ E₃(S)`). -/
def suslinMonicLocal_Good {S : Type*} [CommRing S] (f g : S) : Prop :=
  ∀ τ : (Matrix (Fin 2) (Fin 2) S)ˣ, Matrix.det (τ : Matrix (Fin 2) (Fin 2) S) = 1 →
    (τ : Matrix (Fin 2) (Fin 2) S) 0 0 = f → (τ : Matrix (Fin 2) (Fin 2) S) 0 1 = g →
    stabilizeUnit (R := S) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) S

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_Good

/-- A `2 × 2` matrix of determinant `1`, as a unit. -/
theorem suslinMonicLocal_exists_unit {S : Type*} [CommRing S] (a b c d : S)
    (h : a * d - b * c = 1) :
    ∃ σ : (Matrix (Fin 2) (Fin 2) S)ˣ, (σ : Matrix (Fin 2) (Fin 2) S) = !![a, b; c, d] :=
  ⟨Matrix.nonsingInvUnit !![a, b; c, d] (by rw [Matrix.det_fin_two_of, h]; exact isUnit_one),
    rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_exists_unit

/-- Right multiplication by an elementary matrix does not change stable elementarity. -/
theorem suslinMonicLocal_stab_of_mul {S : Type*} [CommRing S]
    (τ E : (Matrix (Fin 2) (Fin 2) S)ˣ) (hE : E ∈ elementaryGroup (Fin 2) S)
    (h : stabilizeUnit (R := S) (κ := Unit) (τ * E) ∈ elementaryGroup (Fin 2 ⊕ Unit) S) :
    stabilizeUnit (R := S) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) S := by
  have hEs : stabilizeUnit (R := S) (κ := Unit) E ∈ elementaryGroup (Fin 2 ⊕ Unit) S :=
    (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := S) ⟨E, hE⟩).2
  have h2 := mul_mem h (inv_mem hEs)
  rwa [map_mul, mul_inv_cancel_right] at h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_stab_of_mul

/-- **Only the first row matters.**  If `τ, σ ∈ SL₂(S)` share their first row and `σ` is stably
elementary, so is `τ`: indeed `τ = x₂₁(τ₁₀ σ₁₁ - τ₁₁ σ₁₀) · σ`. -/
theorem suslinMonicLocal_stab_of_row {S : Type*} [CommRing S]
    (τ σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (hτ : Matrix.det (τ : Matrix (Fin 2) (Fin 2) S) = 1)
    (hσ : Matrix.det (σ : Matrix (Fin 2) (Fin 2) S) = 1)
    (h0 : (τ : Matrix (Fin 2) (Fin 2) S) 0 0 = (σ : Matrix (Fin 2) (Fin 2) S) 0 0)
    (h1 : (τ : Matrix (Fin 2) (Fin 2) S) 0 1 = (σ : Matrix (Fin 2) (Fin 2) S) 0 1)
    (hs : stabilizeUnit (R := S) (κ := Unit) σ ∈ elementaryGroup (Fin 2 ⊕ Unit) S) :
    stabilizeUnit (R := S) (κ := Unit) τ ∈ elementaryGroup (Fin 2 ⊕ Unit) S := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨E, hE⟩ : ∃ E : (Matrix (Fin 2) (Fin 2) S)ˣ, E = elementaryUnit (1 : Fin 2) 0 h10
      ((τ : Matrix (Fin 2) (Fin 2) S) 1 0 * (σ : Matrix (Fin 2) (Fin 2) S) 1 1 -
        (τ : Matrix (Fin 2) (Fin 2) S) 1 1 * (σ : Matrix (Fin 2) (Fin 2) S) 1 0) := ⟨_, rfl⟩
  have hEmem : E ∈ elementaryGroup (Fin 2) S := by
    rw [hE]
    exact elementaryUnit_mem _ _ _ _
  have hτ' := hτ
  have hσ' := hσ
  rw [Matrix.det_fin_two] at hτ' hσ'
  rw [h0, h1] at hτ'
  have e00 : ((E * σ : (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) 0 0 =
      (τ : Matrix (Fin 2) (Fin 2) S) 0 0 := by
    rw [hE, Units.val_mul, elementaryUnit_mul_apply, if_neg h01, h0]
  have e01 : ((E * σ : (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) 0 1 =
      (τ : Matrix (Fin 2) (Fin 2) S) 0 1 := by
    rw [hE, Units.val_mul, elementaryUnit_mul_apply, if_neg h01, h1]
  have e10 : ((E * σ : (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) 1 0 =
      (τ : Matrix (Fin 2) (Fin 2) S) 1 0 := by
    rw [hE, Units.val_mul, elementaryUnit_mul_apply, if_pos rfl]
    linear_combination (τ : Matrix (Fin 2) (Fin 2) S) 1 0 * hσ' -
      (σ : Matrix (Fin 2) (Fin 2) S) 1 0 * hτ'
  have e11 : ((E * σ : (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) 1 1 =
      (τ : Matrix (Fin 2) (Fin 2) S) 1 1 := by
    rw [hE, Units.val_mul, elementaryUnit_mul_apply, if_pos rfl]
    linear_combination (τ : Matrix (Fin 2) (Fin 2) S) 1 1 * hσ' -
      (σ : Matrix (Fin 2) (Fin 2) S) 1 1 * hτ'
  have hEq : τ = E * σ := by
    refine Units.ext ?_
    rw [Matrix.eta_fin_two (τ : Matrix (Fin 2) (Fin 2) S),
      Matrix.eta_fin_two ((E * σ : (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S),
      e00, e01, e10, e11]
  have hEs : stabilizeUnit (R := S) (κ := Unit) E ∈ elementaryGroup (Fin 2 ⊕ Unit) S :=
    (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := S) ⟨E, hEmem⟩).2
  rw [hEq, map_mul]
  exact mul_mem hEs hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_stab_of_row

/-- **Unit pivot.**  A first row with a unit `(0,0)` entry is good. -/
theorem suslinMonicLocal_good_of_isUnit {S : Type*} [CommRing S] {f : S} (g : S)
    (hf : IsUnit f) : suslinMonicLocal_Good f g := by
  intro τ hdet h0 _
  have hmem := suslinBase3Cong_mem_of_isUnit τ hdet (by rw [h0]; exact hf)
  exact (elementaryStabilization (ι := Fin 2) (κ := Unit) (R := S) ⟨τ, hmem⟩).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_of_isUnit

/-- **Column move on the second entry.**  `(f, g)` is good once `(f, g + f t)` is. -/
theorem suslinMonicLocal_colRight {S : Type*} [CommRing S] {f g g' : S} (t : S)
    (h : suslinMonicLocal_Good f g') (hg : g' = g + f * t) : suslinMonicLocal_Good f g := by
  intro τ hdet h0 h1
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨E, hE⟩ : ∃ E : (Matrix (Fin 2) (Fin 2) S)ˣ, E = elementaryUnit (0 : Fin 2) 1 h01 t :=
    ⟨_, rfl⟩
  have hEmem : E ∈ elementaryGroup (Fin 2) S := by
    rw [hE]
    exact elementaryUnit_mem _ _ _ _
  refine suslinMonicLocal_stab_of_mul τ E hEmem (h (τ * E) ?_ ?_ ?_)
  · rw [Units.val_mul, Matrix.det_mul, hdet, suslin_det_eq_one_of_mem_elementaryGroup hEmem,
      one_mul]
  · rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_neg h01, h0]
  · rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, h0, h1, hg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_colRight

/-- **Column move on the first entry.**  `(f, g)` is good once `(f + g t, g)` is. -/
theorem suslinMonicLocal_colLeft {S : Type*} [CommRing S] {f f' g : S} (t : S)
    (h : suslinMonicLocal_Good f' g) (hf : f' = f + g * t) : suslinMonicLocal_Good f g := by
  intro τ hdet h0 h1
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  obtain ⟨E, hE⟩ : ∃ E : (Matrix (Fin 2) (Fin 2) S)ˣ, E = elementaryUnit (1 : Fin 2) 0 h10 t :=
    ⟨_, rfl⟩
  have hEmem : E ∈ elementaryGroup (Fin 2) S := by
    rw [hE]
    exact elementaryUnit_mem _ _ _ _
  refine suslinMonicLocal_stab_of_mul τ E hEmem (h (τ * E) ?_ ?_ ?_)
  · rw [Units.val_mul, Matrix.det_mul, hdet, suslin_det_eq_one_of_mem_elementaryGroup hEmem,
      one_mul]
  · rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_pos rfl, h0, h1, hf]
  · rw [hE, Units.val_mul, mul_elementaryUnit_apply, if_neg h10, h1]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_colLeft

/-- **Swap.**  `(f, g)` is good once `(g, -f)` is (three column moves). -/
theorem suslinMonicLocal_good_of_swap {S : Type*} [CommRing S] {f g h : S}
    (H : suslinMonicLocal_Good g h) (hh : h = -f) : suslinMonicLocal_Good f g := by
  refine suslinMonicLocal_colRight (g' := g + f * (-1)) (-1) ?_ rfl
  refine suslinMonicLocal_colLeft (f' := g) 1 ?_ (by ring)
  exact suslinMonicLocal_colRight (-1) H (by rw [hh]; ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_of_swap

/-- **Swap, forward form.**  If `(f, g)` is good, so is `(g, -f)`. -/
theorem suslinMonicLocal_good_swap {S : Type*} [CommRing S] {f g : S}
    (H : suslinMonicLocal_Good f g) : suslinMonicLocal_Good g (-f) := by
  have h1 : suslinMonicLocal_Good (-g) f := suslinMonicLocal_good_of_swap H (neg_neg g).symm
  have h2 : suslinMonicLocal_Good (-f) (-g) :=
    suslinMonicLocal_good_of_swap h1 (neg_neg f).symm
  exact suslinMonicLocal_good_of_swap h2 rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_swap

/-- A first row with a unit `(0,1)` entry is good. -/
theorem suslinMonicLocal_good_unitRight {S : Type*} [CommRing S] (f : S) {g : S}
    (hg : IsUnit g) : suslinMonicLocal_Good f g :=
  suslinMonicLocal_good_of_swap (suslinMonicLocal_good_of_isUnit (-f) hg) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_unitRight

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
