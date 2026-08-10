import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Countable

/-!
# Reducing subgroup intersections in a countable group

An arbitrary family of subgroups of a countable group has a countable
subfamily with the same intersection.  The proof chooses, for every element
outside the total intersection, one subgroup which excludes that element.

This is the purely algebraic countability step in intersection-permanence
arguments for relative approximation properties.  It has no approximation,
amenability, or operator-algebraic hypotheses.
-/

namespace NonsoficGroupsExist

open scoped Pointwise

variable {G : Type*} [Group G]

/-- In a countable group, an arbitrary intersection of subgroups is already
the intersection of a countable subfamily. -/
theorem Subgroup.exists_countable_subfamily_iInf_eq [Countable G]
    {I : Type*} (K : I → Subgroup G) :
    ∃ J : Set I, Set.Countable J ∧ (⨅ j : J, K j.1) = ⨅ i, K i := by
  classical
  let total : Subgroup G := ⨅ i, K i
  let bad : Set G := {g | g ∉ total}
  have hexclude : ∀ g : bad, ∃ i, (g : G) ∉ K i := by
    intro g
    have hg : (g : G) ∉ ⨅ i, K i := by
      have hbad := g.property
      change (g : G) ∉ total at hbad
      simpa only [total] using hbad
    simpa only [Subgroup.mem_iInf, not_forall] using hg
  let exclude : bad → I := fun g ↦ Classical.choose (hexclude g)
  have hexclude_spec (g : bad) : (g : G) ∉ K (exclude g) :=
    Classical.choose_spec (hexclude g)
  let J : Set I := Set.range exclude
  refine ⟨J, Set.countable_range exclude, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [Subgroup.mem_iInf] at hg
    rw [Subgroup.mem_iInf]
    intro i
    by_contra hgi
    have hbad : g ∈ bad := by
      simpa only [bad, total, Subgroup.mem_iInf, not_forall] using ⟨i, hgi⟩
    let gbad : bad := ⟨g, hbad⟩
    have hJ : exclude gbad ∈ J := ⟨gbad, rfl⟩
    have hmem : g ∈ K (exclude gbad) := by
      have := hg ⟨exclude gbad, hJ⟩
      simpa only using this
    exact hexclude_spec gbad hmem
  · exact le_iInf fun j ↦ iInf_le K j.1

end NonsoficGroupsExist
