import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalGood
import GroupApproximation.Meta.AxiomGuard

/-!
# Multiplicativity of good first rows (Mennicke product rule)

Lane `bh-met-93i`.  Over every commutative ring `S`:
* `(a, b₁)` and `(a, b₂)` good imply `(a, b₁ b₂)` good (`suslinMonicLocal_good_mul_right`);
* `(a₁, b)` and `(-a₂, b)` good imply `(a₁ a₂, b)` good (`suslinMonicLocal_good_mul_left`).
Route: given `τ` with first row `(a, b₁ b₂)` and second row `(c, d)`, the matrices
`σ₁ = [[a, b₁], [b₂ c, d]]`, `σ₂ = [[a, b₂], [b₁ c, d]]` lie in `SL₂(S)`, and the rank-3
Mennicke-type identity of lane `bh-met-92r` (`suslinCongPow_stab_mem_mennicke`) makes
`σ₁₂ = [[a, b₁ b₂], [-(b₂ c)(b₁ c), d - b₁ c d b₂]]` stably elementary; `σ₁₂` has the same first
row as `τ` (`suslinMonicLocal_stab_of_row`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Mennicke product rule in the second entry.** -/
theorem suslinMonicLocal_good_mul_right {S : Type*} [CommRing S] {a b₁ b₂ : S}
    (h₁ : suslinMonicLocal_Good a b₁) (h₂ : suslinMonicLocal_Good a b₂) :
    suslinMonicLocal_Good a (b₁ * b₂) := by
  intro τ hdet h0 h1
  obtain ⟨c, hc⟩ : ∃ c : S, (τ : Matrix (Fin 2) (Fin 2) S) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : S, (τ : Matrix (Fin 2) (Fin 2) S) 1 1 = d := ⟨_, rfl⟩
  have H : a * d - b₁ * b₂ * c = 1 := by
    have h := hdet
    rw [Matrix.det_fin_two, h0, h1, hc, hd] at h
    exact h
  have H1 : a * d - b₁ * (b₂ * c) = 1 := by linear_combination H
  have H2 : a * d - b₂ * (b₁ * c) = 1 := by linear_combination H
  have H12 : a * (d - b₁ * c * d * b₂) - b₁ * b₂ * -(b₂ * c * (b₁ * c)) = 1 := by
    linear_combination (1 - b₁ * b₂ * c) * H
  obtain ⟨σ₁, hσ1⟩ := suslinMonicLocal_exists_unit a b₁ (b₂ * c) d H1
  obtain ⟨σ₂, hσ2⟩ := suslinMonicLocal_exists_unit a b₂ (b₁ * c) d H2
  obtain ⟨σ₁₂, hσ12⟩ := suslinMonicLocal_exists_unit a (b₁ * b₂) (-(b₂ * c * (b₁ * c)))
    (d - b₁ * c * d * b₂) H12
  have hx : stabilizeUnit (R := S) (κ := Unit) σ₁ ∈ elementaryGroup (Fin 2 ⊕ Unit) S :=
    h₁ σ₁ (by rw [hσ1, Matrix.det_fin_two_of]; exact H1)
      ((congrFun (congrFun hσ1 0) 0).trans rfl) ((congrFun (congrFun hσ1 0) 1).trans rfl)
  have hy : stabilizeUnit (R := S) (κ := Unit) σ₂ ∈ elementaryGroup (Fin 2 ⊕ Unit) S :=
    h₂ σ₂ (by rw [hσ2, Matrix.det_fin_two_of]; exact H2)
      ((congrFun (congrFun hσ2 0) 0).trans rfl) ((congrFun (congrFun hσ2 0) 1).trans rfl)
  have hz := suslinCongPow_stab_mem_mennicke σ₁ σ₂ σ₁₂ H1 hσ1 hσ2 hσ12 hx hy
  have e0 : (σ₁₂ : Matrix (Fin 2) (Fin 2) S) 0 0 = a := (congrFun (congrFun hσ12 0) 0).trans rfl
  have e1 : (σ₁₂ : Matrix (Fin 2) (Fin 2) S) 0 1 = b₁ * b₂ :=
    (congrFun (congrFun hσ12 0) 1).trans rfl
  exact suslinMonicLocal_stab_of_row τ σ₁₂ hdet
    (by rw [hσ12, Matrix.det_fin_two_of]; exact H12) (h0.trans e0.symm) (h1.trans e1.symm) hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_mul_right

/-- **Mennicke product rule in the first entry.** -/
theorem suslinMonicLocal_good_mul_left {S : Type*} [CommRing S] {a₁ a₂ b : S}
    (h₁ : suslinMonicLocal_Good a₁ b) (h₂ : suslinMonicLocal_Good (-a₂) b) :
    suslinMonicLocal_Good (a₁ * a₂) b := by
  have k₁ : suslinMonicLocal_Good b (-a₁) := suslinMonicLocal_good_swap h₁
  have k₂ : suslinMonicLocal_Good b a₂ := by
    have k := suslinMonicLocal_good_swap h₂
    rwa [neg_neg] at k
  exact suslinMonicLocal_good_of_swap (suslinMonicLocal_good_mul_right k₁ k₂) (by ring)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_good_mul_left

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
