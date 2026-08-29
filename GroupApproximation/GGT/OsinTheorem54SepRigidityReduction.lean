import GroupApproximation.GGT.OsinTheorem54SepFourGonCorner

/-!
# One peripheral letter as a component

Two small facts about the one-letter word `[comp s g]`: it is a component of
itself, and its far vertex is `g`.  They are what turns a conjugation equation

  `x * a s ^ i * x' = a s ^ j`

into a quadrilateral with the two deep powers as its long sides --- each power
is a single peripheral letter, hence a one-letter component --- which is how the
rigidity clause is proved.

The rigidity clause itself is `mem_fam_of_conj_of_deep_six` in
`GGT/OsinTheorem54SepDeepSixForm.lean`.  It used to be here, over the
unrestricted `IsolatedComponentBound`; that version is deleted.  It asserted the
isolated-component bound at every number of sides, which is strictly more than
anything proved in this repository, and its only consumer now takes the
six-side form.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u

variable {G : Type u} [Group G]

omit [Group G] in
/-- A single peripheral letter is a one-letter component. -/
theorem isComp_singleton (s : Bool) (g : G) :
    IsComp s [RelLetter.comp s g] 0 1 := by
  refine ⟨by omega, by simp, ?_, ?_, ?_⟩
  · intro t ht1 ht2 ht
    have ht0 : t = 0 := by omega
    subst ht0
    exact rfl
  · intro t ht
    omega
  · intro hk
    simp at hk

/-- The far vertex of a one-letter word is its letter's value. -/
theorem vertex_singleton_one (s : Bool) (g : G) :
    vertex (1 : G) [RelLetter.comp s g] 1 = g := by
  rw [vertex_cons_succ, vertex_zero, one_mul]
  rfl

end OsinComponents
end GGT
end GroupApproximation
