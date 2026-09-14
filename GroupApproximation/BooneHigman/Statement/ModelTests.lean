/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BooneHigman.Statement.API
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Model tests for the Boone–Higman statement definitions

Each definition of `Statement/Basic.lean` is tested on a positive and a negative model, so that a
vacuous or always-true definition cannot pass.

* `IsMetabelianGroup`: `S₃` is metabelian and not commutative (`perm_three_isMetabelianGroup`,
  `perm_three_not_commutative`); `S₅` is not metabelian (`perm_five_not_isMetabelianGroup`).
* `IsSimpleGroup` as used in the statements: `A₅` is simple; `S₃` is not.
* `EmbedsInFinitelyPresentedSimpleGroup`: `A₅` embeds (in itself); `Multiplicative ℝ` does not,
  because a finitely presented group is countable.
-/

namespace GroupApproximation.BooneHigman.ModelTests

open Equiv

theorem alternatingGroup_three_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- Elements of `A₃`, a group of prime order, commute. -/
theorem alternatingGroup_three_mul_comm {a b : Perm (Fin 3)} (ha : a ∈ alternatingGroup (Fin 3))
    (hb : b ∈ alternatingGroup (Fin 3)) : a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := isCyclic_of_prime_card alternatingGroup_three_card
  letI := IsCyclic.commGroup (α := alternatingGroup (Fin 3))
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : alternatingGroup (Fin 3)) ⟨b, hb⟩)

/-- **Positive model.** `S₃` is metabelian: `S₃' ≤ A₃`, and `A₃` is commutative. -/
theorem perm_three_isMetabelianGroup : IsMetabelianGroup (Perm (Fin 3)) := by
  refine isMetabelianGroup_of_commutator_le (N := alternatingGroup (Fin 3)) ?_ ?_
  · rw [alternatingGroup_eq_sign_ker, commutator, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact alternatingGroup_three_mul_comm ha hb

/-- `S₃` is not commutative, so the positive model is not an abelian one. -/
theorem perm_three_not_commutative : ¬ ∀ a b : Perm (Fin 3), a * b = b * a := fun h ↦
  absurd (h (swap 0 1) (swap 1 2)) (by decide)

/-- **Negative model.** `S₅` is not metabelian: it is not even solvable. -/
theorem perm_five_not_isMetabelianGroup : ¬ IsMetabelianGroup (Perm (Fin 5)) := fun h ↦
  Perm.fin_5_not_solvable h.isSolvable

/-- **Positive model.** `A₅` is simple. -/
theorem alternatingGroup_five_isSimpleGroup : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  inferInstance

/-- **Negative model.** `S₃` is not simple: `A₃` is a normal subgroup of order `3`. -/
theorem perm_three_not_isSimpleGroup : ¬ IsSimpleGroup (Perm (Fin 3)) := by
  intro h
  have hcard := alternatingGroup_three_card
  rcases h.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 3)) inferInstance with h1 | h1
  · rw [h1, Subgroup.card_bot] at hcard
    exact absurd hcard (by decide)
  · rw [h1, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin] at hcard
    exact absurd hcard (by decide)

/-- **Positive model.** `A₅` embeds in a finitely presented simple group, namely itself. -/
theorem alternatingGroup_five_embeds :
    EmbedsInFinitelyPresentedSimpleGroup (alternatingGroup (Fin 5)) :=
  embedsInFinitelyPresentedSimpleGroup_of_injective (S := alternatingGroup (Fin 5))
    (f := MonoidHom.id _) Function.injective_id

/-- **Negative model.** An uncountable group embeds in no finitely presented group. -/
theorem multiplicative_real_not_embeds :
    ¬ EmbedsInFinitelyPresentedSimpleGroup (Multiplicative ℝ) := by
  intro h
  haveI : Countable (Multiplicative ℝ) := h.countable
  haveI : Countable ℝ := (Multiplicative.ofAdd (α := ℝ)).injective.countable
  exact Uncountable.not_countable (α := ℝ) inferInstance

end GroupApproximation.BooneHigman.ModelTests
