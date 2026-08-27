import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.PropertyTT.Basic

/-!
# Transporting relative `(TT)/T` along index permutations
-/

namespace GroupApproximation

universe v

variable {R I J : Type*} [Ring R]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Reindexing maps an elementary root subgroup exactly onto the
corresponding reindexed root subgroup. -/
theorem elementaryRootSubgroup_map_reindex
    (e : I ≃ J) (i j : I) (hij : i ≠ j) :
    (elementaryRootSubgroup (R := R) i j hij).map
        (elementaryReindexEquiv (R := R) e).toMonoidHom =
      elementaryRootSubgroup (e i) (e j) (e.injective.ne hij) := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (elementaryReindexEquiv_elementaryRoot
      e i j hij a).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨elementaryRoot i j hij a, ⟨a, rfl⟩,
      elementaryReindexEquiv_elementaryRoot e i j hij a⟩

/-- Relative `(TT)/T` for a root transports along an arbitrary index
equivalence. -/
theorem HasRelativeTTmodT.reindexRoot
    (e : I ≃ J) (i j : I) (hij : i ≠ j)
    (hrel : HasRelativeTTmodT.{_, v}
      (elementaryGroup I R) (elementaryRootSubgroup i j hij)) :
    HasRelativeTTmodT.{_, v}
      (elementaryGroup J R)
      (elementaryRootSubgroup (e i) (e j) (e.injective.ne hij)) := by
  apply HasRelativeTTmodT.of_surjective
    (elementaryReindexEquiv (R := R) e).toMonoidHom
    (elementaryReindexEquiv (R := R) e).surjective
    (elementaryRootSubgroup i j hij)
    (elementaryRootSubgroup (e i) (e j) (e.injective.ne hij))
  · rw [elementaryRootSubgroup_map_reindex]
  · exact hrel

end GroupApproximation
