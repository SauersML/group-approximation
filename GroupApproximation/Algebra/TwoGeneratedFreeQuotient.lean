import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# A two-generated group is a quotient of the rank-two free group

This elementary module is kept independent of the MF and small-cancellation
development so the quotient map can be reused without importing analytic
machinery.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- The rank-two free-group map determined by an ordered pair. -/
def twoGeneratorFreeGroupMap (x y : G) : FreeGroup (Fin 2) →* G :=
  FreeGroup.lift (fun i ↦ if i = 0 then x else y)

/-- If the ordered pair generates the target, its rank-two free-group map is
surjective. -/
theorem twoGeneratorFreeGroupMap_surjective {x y : G}
    (hxy : Subgroup.closure ({x, y} : Set G) = ⊤) :
    Function.Surjective (twoGeneratorFreeGroupMap x y) := by
  let f := twoGeneratorFreeGroupMap x y
  have htop : f.range = ⊤ := by
    apply top_unique
    rw [← hxy]
    refine (Subgroup.closure_le f.range).2 ?_
    intro z hz
    rcases hz with hz | hz
    · subst z
      refine ⟨FreeGroup.of 0, ?_⟩
      simp [f, twoGeneratorFreeGroupMap]
    · have hz' : z = y := by simpa using hz
      subst z
      refine ⟨FreeGroup.of 1, ?_⟩
      simp [f, twoGeneratorFreeGroupMap]
  intro q
  have hq : q ∈ f.range := by
    rw [htop]
    exact Subgroup.mem_top q
  exact hq

end GroupApproximation
