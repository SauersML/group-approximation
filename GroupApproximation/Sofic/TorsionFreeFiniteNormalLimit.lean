import Mathlib.GroupTheory.OrderOfElement

/-!
# Why a finite-normal obstruction cannot itself be torsion-free

The finite-normal Kazhdan-compression criterion detects an element in a
finite subgroup.  In a torsion-free group every such subgroup is trivial,
so this particular criterion cannot directly furnish a nontrivial marked
obstruction in a torsion-free ambient group.
-/

namespace GroupApproximation

universe u

/-- Every finite subgroup of every torsion-free group is trivial.  The
statement is closed: the group, its instances, and the subgroup are all
quantified inside the proposition. -/
theorem finiteSubgroup_eq_bot_of_isMulTorsionFree :
    ∀ (G : Type u) [Group G] [IsMulTorsionFree G]
      (F : Subgroup G) [Finite F], F = ⊥ := by
  intro G _ _ F _
  apply (Subgroup.eq_bot_iff_forall F).mpr
  intro x hx
  let y : F := ⟨x, hx⟩
  have hy : IsOfFinOrder y := isOfFinOrder_of_finite y
  exact congrArg Subtype.val hy.eq_one'

end GroupApproximation
