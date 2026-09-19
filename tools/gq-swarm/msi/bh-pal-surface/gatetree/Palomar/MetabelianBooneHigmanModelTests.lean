/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Palomar.MetabelianBooneHigmanSolution
import GroupApproximation.BooneHigman.Statement.ModelTests

/-!
# Model tests for the metabelian Boone–Higman shared block

Each definition of the shared block of `Palomar/MetabelianBooneHigmanChallenge.lean`
is tested on a positive and a negative model, so that a vacuous or always-true
definition cannot pass.  The copies tested here are the solution's, which are
byte-identical to the challenge's.

* `IsMetabelianGroup`: `ℤ` and `S₃` are metabelian; `S₅` is not.
* `EmbedsInFinitelyPresentedSimpleGroup`: `A₅` embeds, in itself; `ℝ` does not,
  because a finitely presented group is countable.
* `not_every_group_embeds`: the embedding property is not universal, so the two
  compared theorems are not vacuous in their conclusion.

The prose of this module was written by Claude (Anthropic).
-/

namespace MetabelianBooneHigman.ModelTests

open Equiv

/-- **Positive model.** `ℤ`, a commutative group, is metabelian. -/
theorem multiplicative_int_isMetabelianGroup : IsMetabelianGroup (Multiplicative ℤ) :=
  isMetabelianGroup_iff.mpr (GroupApproximation.BooneHigman.isMetabelianGroup_of_commute mul_comm)

/-- **Positive model.** `S₃`, which is not commutative, is metabelian. -/
theorem perm_three_isMetabelianGroup : IsMetabelianGroup (Perm (Fin 3)) :=
  isMetabelianGroup_iff.mpr GroupApproximation.BooneHigman.ModelTests.perm_three_isMetabelianGroup

/-- **Negative model.** `S₅` is not metabelian. -/
theorem perm_five_not_isMetabelianGroup : ¬ IsMetabelianGroup (Perm (Fin 5)) := fun h ↦
  GroupApproximation.BooneHigman.ModelTests.perm_five_not_isMetabelianGroup
    (isMetabelianGroup_iff.mp h)

/-- **Positive model.** `A₅` embeds in a finitely presented simple group. -/
theorem alternatingGroup_five_embeds :
    EmbedsInFinitelyPresentedSimpleGroup (alternatingGroup (Fin 5)) :=
  embedsInFinitelyPresentedSimpleGroup_iff.mpr
    GroupApproximation.BooneHigman.ModelTests.alternatingGroup_five_embeds

/-- **Negative model.** `ℝ` embeds in no finitely presented simple group. -/
theorem multiplicative_real_not_embeds :
    ¬ EmbedsInFinitelyPresentedSimpleGroup (Multiplicative ℝ) := fun h ↦
  GroupApproximation.BooneHigman.ModelTests.multiplicative_real_not_embeds
    (embedsInFinitelyPresentedSimpleGroup_iff.mp h)

/-- The conclusion of the compared theorems is not universal. -/
theorem not_every_group_embeds :
    ¬ ∀ (G : Type) [Group G], EmbedsInFinitelyPresentedSimpleGroup G := fun h ↦
  multiplicative_real_not_embeds (h (Multiplicative ℝ))

end MetabelianBooneHigman.ModelTests
