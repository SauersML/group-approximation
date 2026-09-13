import GroupApproximation.ThompsonOre.ShiftOre
import GroupApproximation.GroupTheory.HigmanThompson.BrownPresentation

/-!
# Guba's Theorem 3.18 for Brown's group `F`

Brown's group `BrownGroup 0` is Thompson's group `F`, with `x_i = X_i⁻¹`.  The elements
`X_i⁻¹` form a positive frame (`brownFrame`): Brown's relation `X_i X_j X_i⁻¹ = X_(j+1)` is
`x_j x_i = x_i x_(j+1)`, every element is `p⁻¹ q` with `p, q` positive (`exists_form`), and a
sorted positive word is read off its evaluation (`sorted_eq_of_eval_eq`).

* `PositiveFrame.map`: a positive frame transports along an isomorphism, so the theorem holds on
  any model of `F` isomorphic to `BrownGroup 0`.
* `brown_exists_ne_zero_one_sub_mul_eq_mul`: Theorem 3.18 on `K[BrownGroup 0]`.
-/

namespace GroupApproximation.ThompsonOre

open MonoidAlgebra HigmanThompson

namespace PositiveFrame

variable {G H : Type*} [Group G] [Group H]

/-- Transport a positive frame along an isomorphism. -/
def map (P : PositiveFrame G) (e : G ≃* H) : PositiveFrame H where
  x i := e (P.x i)
  rel i j h := by rw [← map_mul, ← map_mul, P.rel i j h]
  closure_eq_top := by
    have hr : Set.range (fun i => e (P.x i)) = (e.toMonoidHom : G →* H) '' Set.range P.x := by
      rw [← Set.range_comp]; rfl
    rw [hr, ← MonoidHom.map_closure, P.closure_eq_top]
    exact Subgroup.map_top_of_surjective _ e.surjective
  sorted_inj l₁ l₂ h₁ h₂ h := by
    refine P.sorted_inj l₁ l₂ h₁ h₂ (e.injective ?_)
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    exact h

end PositiveFrame

theorem prod_map_inv_brownX :
    ∀ l : List ℕ, (l.map fun i => (brownX 0 i)⁻¹).prod = (brownPos 0 l)⁻¹
  | [] => by
    show (1 : BrownGroup 0) = (1 : BrownGroup 0)⁻¹
    exact inv_one.symm
  | i :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_inv_brownX l]
    show _ = (brownPos 0 l * brownX 0 i)⁻¹
    rw [mul_inv_rev]

theorem brownPos_mem_closure (l : List ℕ) :
    brownPos 0 l ∈ Subgroup.closure (Set.range fun i => (brownX 0 i)⁻¹) := by
  have hmem : (l.map fun i => (brownX 0 i)⁻¹).prod ∈
      Subgroup.closure (Set.range fun i => (brownX 0 i)⁻¹) :=
    list_prod_mem fun y hy => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      exact Subgroup.subset_closure ⟨i, rfl⟩
  rw [prod_map_inv_brownX] at hmem
  simpa using inv_mem hmem

/-- The positive frame `x_i = X_i⁻¹` of Brown's group `BrownGroup 0`. -/
def brownFrame : PositiveFrame (BrownGroup 0) where
  x i := (brownX 0 i)⁻¹
  rel i j h := by
    have hrel := brownX_rel 0 h
    simp only [add_zero] at hrel
    rw [← hrel]
    group
  closure_eq_top := by
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨q, p, rfl⟩ := exists_form 0 g
    exact mul_mem (inv_mem (brownPos_mem_closure q)) (brownPos_mem_closure p)
  sorted_inj l₁ l₂ h₁ h₂ h := by
    rw [prod_map_inv_brownX, prod_map_inv_brownX, inv_inj] at h
    exact sorted_eq_of_eval_eq 0 l₁ l₂ h₁ h₂ (congrArg (brownEval 0) h)

/-- **Guba's Theorem 3.18 for `F = BrownGroup 0`.** With `x_0 = X_0⁻¹`, every `b ∈ K[F]` has
`v ≠ 0` with `b v ∈ (1 - x_0) K[F]`. -/
theorem brown_exists_ne_zero_one_sub_mul_eq_mul {K : Type*} [Field K]
    (b : MonoidAlgebra K (BrownGroup 0)) :
    ∃ u v : MonoidAlgebra K (BrownGroup 0), v ≠ 0 ∧
      (1 - of K (BrownGroup 0) (brownX 0 0)⁻¹) * u = b * v :=
  brownFrame.exists_ne_zero_one_sub_x_zero_mul_eq_mul b

end GroupApproximation.ThompsonOre
