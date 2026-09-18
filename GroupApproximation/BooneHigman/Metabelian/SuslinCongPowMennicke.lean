import GroupApproximation.BooneHigman.Metabelian.SuslinCongPowVal
import GroupApproximation.Meta.AxiomGuard

/-!
# A rank-3 Mennicke-type product identity, over every commutative ring

Lane `bh-met-92r`.  Let `S` be any commutative ring and let
`σ₁ = [[a, b₁], [c₁, d₁]]`, `σ₂ = [[a, b₂], [c₂, d₂]]` be invertible with `a d₁ - b₁ c₁ = 1`.
Put `σ₁₂ = [[a, b₁ b₂], [-c₁ c₂, d₂ - c₂ d₁ b₂]]` (invertible too).  Then in `GL₃(S)`
(indices `1 = inl 0`, `2 = inl 1`, `3 = inr ()`):

`σ₁₂ in coordinates (1, 3) = E₃₂(-c₂) · diag(σ₁, 1) · (σ₂ in coordinates (2, 3)) ·`
`E₁₂(-b₁) · E₂₁(-c₁) · E₂₃(-d₁ b₂)`   (`suslinCongPow_mennicke_eq`).

Consequently (`suslinCongPow_stab_mem_mennicke`): if `diag(σ₁, 1)` and `diag(σ₂, 1)` lie in
`E₃(S)`, so does `diag(σ₁₂, 1)`.  Only `a d₁ - b₁ c₁ = 1` is used; no hypothesis on `S`.  The
identity was checked symbolically (sympy, `$SP/bh-met-92r/mennicke.py`): the difference of the
two sides is `(a d₁ - b₁ c₁ - 1)` times an explicit matrix.
-/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **The rank-3 Mennicke-type product identity.** -/
theorem suslinCongPow_mennicke_eq {S : Type*} [CommRing S]
    (σ1 σ2 σ12 : (Matrix (Fin 2) (Fin 2) S)ˣ) {a b1 c1 d1 b2 c2 d2 : S}
    (h1 : a * d1 - b1 * c1 = 1)
    (hσ1 : (σ1 : Matrix (Fin 2) (Fin 2) S) = !![a, b1; c1, d1])
    (hσ2 : (σ2 : Matrix (Fin 2) (Fin 2) S) = !![a, b2; c2, d2])
    (hσ12 : (σ12 : Matrix (Fin 2) (Fin 2) S) =
      !![a, b1 * b2; -(c1 * c2), d2 - c2 * d1 * b2]) :
    elementaryReindexUnitEquiv (R := S) suslinCongPow_e₂
        (stabilizeUnit (R := S) (κ := Unit) σ12) =
      elementaryUnit (ι := Fin 2 ⊕ Unit) (R := S) (Sum.inr ()) (Sum.inl 1) Sum.inr_ne_inl
          (-c2) *
        stabilizeUnit (R := S) (κ := Unit) σ1 *
        elementaryReindexUnitEquiv (R := S) suslinCongPow_e₁
          (stabilizeUnit (R := S) (κ := Unit) σ2) *
        elementaryUnit (ι := Fin 2 ⊕ Unit) (R := S) (Sum.inl 0) (Sum.inl 1) (by decide) (-b1) *
        elementaryUnit (ι := Fin 2 ⊕ Unit) (R := S) (Sum.inl 1) (Sum.inl 0) (by decide) (-c1) *
        elementaryUnit (ι := Fin 2 ⊕ Unit) (R := S) (Sum.inl 1) (Sum.inr ()) Sum.inl_ne_inr
          (-(d1 * b2)) := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [suslinCongPow_e₂_stab_val σ12 hσ12, suslinCongPow_stab_val σ1 hσ1,
    suslinCongPow_e₁_stab_val σ2 hσ2, suslinCongPow_eU32_val, suslinCongPow_eU12_val,
    suslinCongPow_eU21_val, suslinCongPow_eU23_val]
  simp only [suslinCongPow_m3_mul, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]
  refine suslinCongPow_m3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
      | ring1
      | linear_combination h1
      | linear_combination (-1 : S) * h1
      | linear_combination c1 * h1
      | linear_combination (-c1) * h1
      | linear_combination c2 * h1
      | linear_combination (-c2) * h1
      | linear_combination (b2 * d1) * h1
      | linear_combination (-(b2 * d1)) * h1
      | linear_combination (c1 * c2) * h1
      | linear_combination (-(c1 * c2)) * h1
      | linear_combination (b2 * c2 * d1) * h1
      | linear_combination (-(b2 * c2 * d1)) * h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_mennicke_eq

/-- A reindexing of an element of `E₃` lies in `E₃`. -/
theorem suslinCongPow_reindex_mem {S : Type*} [CommRing S] (e : Fin 2 ⊕ Unit ≃ Fin 2 ⊕ Unit)
    {u : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ}
    (hu : u ∈ elementaryGroup (Fin 2 ⊕ Unit) S) :
    elementaryReindexUnitEquiv (R := S) e u ∈ elementaryGroup (Fin 2 ⊕ Unit) S := by
  rw [← elementaryReindexGroup_map (R := S) e]
  exact Subgroup.mem_map_of_mem _ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_reindex_mem

/-- An element of `E₃` whose reindexing lies in `E₃` lies in `E₃`. -/
theorem suslinCongPow_mem_of_reindex_mem {S : Type*} [CommRing S]
    (e : Fin 2 ⊕ Unit ≃ Fin 2 ⊕ Unit) {u : (Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) S)ˣ}
    (hu : elementaryReindexUnitEquiv (R := S) e u ∈ elementaryGroup (Fin 2 ⊕ Unit) S) :
    u ∈ elementaryGroup (Fin 2 ⊕ Unit) S := by
  rw [← elementaryReindexGroup_map (R := S) e, Subgroup.mem_map] at hu
  obtain ⟨v, hv, hve⟩ := hu
  have hve' : elementaryReindexUnitEquiv (R := S) e v = elementaryReindexUnitEquiv (R := S) e u :=
    hve
  rw [← (elementaryReindexUnitEquiv (R := S) e).injective hve']
  exact hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_mem_of_reindex_mem

/-- **Mennicke closure of the stabilization into `E₃`**, over every commutative ring. -/
theorem suslinCongPow_stab_mem_mennicke {S : Type*} [CommRing S]
    (σ1 σ2 σ12 : (Matrix (Fin 2) (Fin 2) S)ˣ) {a b1 c1 d1 b2 c2 d2 : S}
    (h1 : a * d1 - b1 * c1 = 1)
    (hσ1 : (σ1 : Matrix (Fin 2) (Fin 2) S) = !![a, b1; c1, d1])
    (hσ2 : (σ2 : Matrix (Fin 2) (Fin 2) S) = !![a, b2; c2, d2])
    (hσ12 : (σ12 : Matrix (Fin 2) (Fin 2) S) =
      !![a, b1 * b2; -(c1 * c2), d2 - c2 * d1 * b2])
    (hx : stabilizeUnit (R := S) (κ := Unit) σ1 ∈ elementaryGroup (Fin 2 ⊕ Unit) S)
    (hy : stabilizeUnit (R := S) (κ := Unit) σ2 ∈ elementaryGroup (Fin 2 ⊕ Unit) S) :
    stabilizeUnit (R := S) (κ := Unit) σ12 ∈ elementaryGroup (Fin 2 ⊕ Unit) S := by
  refine suslinCongPow_mem_of_reindex_mem suslinCongPow_e₂ ?_
  rw [suslinCongPow_mennicke_eq σ1 σ2 σ12 h1 hσ1 hσ2 hσ12]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (elementaryUnit_mem _ _ _ _) hx)
    (suslinCongPow_reindex_mem suslinCongPow_e₁ hy)) (elementaryUnit_mem _ _ _ _))
    (elementaryUnit_mem _ _ _ _)) (elementaryUnit_mem _ _ _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_stab_mem_mennicke

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
