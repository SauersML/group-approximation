import GroupApproximation.CuTensor.CuZModel
import Mathlib.Topology.Order.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The compact elements of the model of `Cu(𝒵)`

The compact elements of `CuZModel` are exactly the classes `cpt n`.  A compact `n` is compact
because every class either dominates it or lies below the soft class `n`, which it does not lie
below.  A soft class `t` is not compact: it is the supremum of an increasing sequence of soft
classes strictly below it.

An isomorphism of Cuntz semigroups is an additive order isomorphism, so it matches compact
elements with compact elements (`orderIso_isCompactElem_iff`).  So an additive isomorphism
`Cu(F) ≅ CuZModel` sends every additive injection `M → Cu(F)` with compact image to an additive
injection `M → ℕ`.  For a stably finite `F`, the Murray--von Neumann semigroup `V(F)` is such an `M`;
that input, and the passage from `V(F) ↪ ℕ` to `K₀(F) ↪ ℤ`, are not proved here.

## Main results

* `CuZModel.isCompactElem_cpt`, `CuZModel.not_isCompactElem_soft`, `CuZModel.isCompactElem_iff`;
* `CuZModel.exists_injective_addMonoidHom_nat`: an additive injection into the model with compact
  image factors through an additive injection into `ℕ`;
* `CuZModel.exists_injective_addMonoidHom_nat_of_orderIso`: the same through an additive order
  isomorphism with the model.
-/

open scoped ENNReal

namespace GroupApproximation
namespace CuTensor
namespace CuZModel

/-- The compact class `0` lies below every class. -/
theorem cpt_zero_le : ∀ x : CuZModel, cpt 0 ≤ x
  | cpt m => cpt_le_cpt.2 (Nat.zero_le m)
  | soft t ht => cpt_le_soft.2 (by rw [Nat.cast_zero]; exact ht)

/-- Every class either dominates the compact class `n` or lies below the soft class `n`. -/
theorem cpt_le_or_le_soft {n : ℕ} (hn : 0 < (n : ℝ≥0∞)) :
    ∀ x : CuZModel, cpt n ≤ x ∨ x ≤ soft (n : ℝ≥0∞) hn
  | cpt m => by
      rcases le_or_gt n m with h | h
      · exact Or.inl (cpt_le_cpt.2 h)
      · exact Or.inr (cpt_le_soft.2 (Nat.cast_lt.2 h))
  | soft t _ => by
      rcases lt_or_ge (n : ℝ≥0∞) t with h | h
      · exact Or.inl (cpt_le_soft.2 h)
      · exact Or.inr (soft_le_soft.2 h)

/-- **The compact classes are compact.** -/
theorem isCompactElem_cpt (n : ℕ) : IsCompactElem (cpt n) := by
  intro f _ s hs hns
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, cpt_zero_le (f 0)⟩
  have hn' : 0 < (n : ℝ≥0∞) := Nat.cast_pos.2 hn
  by_contra hno
  have hub : soft (n : ℝ≥0∞) hn' ∈ upperBounds (Set.range f) := by
    rintro _ ⟨k, rfl⟩
    rcases cpt_le_or_le_soft hn' (f k) with h | h
    · exact (hno ⟨k, h⟩).elim
    · exact h
  exact lt_irrefl _ (cpt_le_soft.1 (hns.trans (hs.2 hub)))

/-- **The soft classes are not compact.** A soft class `t` is the supremum of an increasing
sequence of soft classes strictly below it. -/
theorem not_isCompactElem_soft (t : ℝ≥0∞) (ht : 0 < t) : ¬ IsCompactElem (soft t ht) := by
  intro hc
  obtain ⟨u, hu, hmem, htend⟩ := exists_seq_strictMono_tendsto' ht
  have hlub : IsLUB (Set.range u) t := isLUB_of_tendsto_atTop hu.monotone htend
  have hpos : ∀ k, 0 < u k := fun k => (hmem k).1
  have hf : IsLUB (Set.range fun k => soft (u k) (hpos k)) (soft t ht) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨k, rfl⟩
      exact soft_le_soft.2 (hmem k).2.le
    · intro x hx
      have hx' : ∀ k, soft (u k) (hpos k) ≤ x := fun k => hx ⟨k, rfl⟩
      cases x with
      | cpt m =>
        refine soft_le_cpt.2 (hlub.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact soft_le_cpt.1 (hx' k)
      | soft v hv =>
        refine soft_le_soft.2 (hlub.2 ?_)
        rintro _ ⟨k, rfl⟩
        exact soft_le_soft.1 (hx' k)
  obtain ⟨k, hk⟩ := hc (fun k => soft (u k) (hpos k))
    (fun i j hij => soft_le_soft.2 (hu.monotone hij)) (soft t ht) hf le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt (soft_le_soft.1 hk) (hmem k).2)

/-- **The compact elements of the model are exactly the classes `cpt n`.** -/
theorem isCompactElem_iff {x : CuZModel} : IsCompactElem x ↔ ∃ n, x = cpt n := by
  refine ⟨fun hx => ?_, ?_⟩
  · cases x with
    | cpt n => exact ⟨n, rfl⟩
    | soft t ht => exact (not_isCompactElem_soft t ht hx).elim
  · rintro ⟨n, rfl⟩
    exact isCompactElem_cpt n

/-- The value of a class: `n` on the compact class `n`, and `0` on soft classes. -/
def cptVal : CuZModel → ℕ
  | cpt n => n
  | soft _ _ => 0

@[simp] theorem cptVal_cpt (n : ℕ) : cptVal (cpt n) = n := rfl

/-- **Compact parts embed in `ℕ`.** An additive injection into the model whose image consists of
compact elements factors through an additive injection into `ℕ`. -/
theorem exists_injective_addMonoidHom_nat {M : Type*} [AddZeroClass M] (g : M →+ CuZModel)
    (hg : Function.Injective g) (hc : ∀ m, IsCompactElem (g m)) :
    ∃ φ : M →+ ℕ, Function.Injective φ ∧ ∀ m, g m = cpt (φ m) := by
  have hval : ∀ m, g m = cpt (cptVal (g m)) := fun m => by
    obtain ⟨n, hn⟩ := isCompactElem_iff.1 (hc m)
    rw [hn, cptVal_cpt]
  refine ⟨{ toFun := fun m => cptVal (g m), map_zero' := ?_, map_add' := ?_ }, ?_, hval⟩
  · show cptVal (g 0) = 0
    rw [map_zero, zero_def, cptVal_cpt]
  · intro m m'
    show cptVal (g (m + m')) = cptVal (g m) + cptVal (g m')
    obtain ⟨a, ha⟩ := isCompactElem_iff.1 (hc m)
    obtain ⟨b, hb⟩ := isCompactElem_iff.1 (hc m')
    rw [map_add, ha, hb, cpt_add_cpt, cptVal_cpt, cptVal_cpt, cptVal_cpt]
  · intro m m' h
    obtain ⟨a, ha⟩ := isCompactElem_iff.1 (hc m)
    obtain ⟨b, hb⟩ := isCompactElem_iff.1 (hc m')
    have hab : a = b := by
      have h' : cptVal (g m) = cptVal (g m') := h
      rwa [ha, hb, cptVal_cpt, cptVal_cpt] at h'
    exact hg (ha.trans (hb.trans (congrArg cpt hab.symm)).symm)

/-- **An additive order isomorphism with the model embeds compact parts in `ℕ`.** If
`e : α ≃o CuZModel` is additive and `j : M →+ α` is an additive injection with compact image,
then `M` embeds additively in `ℕ`. -/
theorem exists_injective_addMonoidHom_nat_of_orderIso {α M : Type*} [Preorder α]
    [AddZeroClass α] [AddZeroClass M] (e : α ≃o CuZModel) (he0 : e 0 = 0)
    (he : ∀ x y, e (x + y) = e x + e y) (j : M →+ α) (hj : Function.Injective j)
    (hc : ∀ m, IsCompactElem (j m)) : ∃ φ : M →+ ℕ, Function.Injective φ := by
  let g : M →+ CuZModel :=
    { toFun := fun m => e (j m)
      map_zero' := by simp only [map_zero, he0]
      map_add' := fun m m' => by simp only [map_add, he] }
  obtain ⟨φ, hφ, _⟩ := exists_injective_addMonoidHom_nat g (e.injective.comp hj)
    (fun m => (orderIso_isCompactElem_iff e).2 (hc m))
  exact ⟨φ, hφ⟩

end CuZModel

end CuTensor
end GroupApproximation
