import GroupApproximation.GGT.VanKampen.PermOrbitTransport

/-!
# Cycles of a permutation restricted to an invariant subtype

A permutation preserving a predicate restricts to the subtype it cuts out, and
two points of the subtype are in the same cycle of the restriction exactly when
they are in the same cycle of the original permutation.

This is used for the darts outside a replaced region: the face rotation
preserves the face of a dart, so it restricts to the darts based outside the
region, and its cycles there are its cycles in the ambient map.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u

/-- A power of a restricted permutation acts by the corresponding power of the
original one. -/
theorem subtypePerm_zpow_val {γ : Type u} (f : Equiv.Perm γ) {P : γ → Prop}
    (h : ∀ x, P (f x) ↔ P x) (i : ℤ) (x : {z : γ // P z}) :
    (((f.subtypePerm h) ^ i) x).1 = (f ^ i) x.1 := by
  rw [Equiv.Perm.subtypePerm_zpow, Equiv.Perm.subtypePerm_apply]

/-- Two points of an invariant subtype are in the same cycle of the restricted
permutation exactly when they are in the same cycle of the original one. -/
theorem sameCycle_subtypePerm {γ : Type u} (f : Equiv.Perm γ) {P : γ → Prop}
    (h : ∀ x, P (f x) ↔ P x) (x y : {z : γ // P z}) :
    Equiv.Perm.SameCycle (f.subtypePerm h) x y ↔
      Equiv.Perm.SameCycle f x.1 y.1 := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [← subtypePerm_zpow_val f h i x, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    rw [subtypePerm_zpow_val f h i x, hi]

end VanKampen
end GGT
end GroupApproximation
