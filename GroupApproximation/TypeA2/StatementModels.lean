/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.TypeA2.Statement
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Coset.Card

/-!
# Model tests for the FFWZ Question 5.8 definitions

Each definition in `GroupApproximation.TypeA2.Statement` is proved on a positive model.
Where it is cheap, it is also refuted on a negative model.

* `IsTypeA2`:
  * holds for every action of a finite group on a finite non-empty set
    (`isTypeA2_of_finite`);
  * fails the non-emptiness clause on the empty set (`not_isTypeA2_empty`);
  * fails the orbit clause for a trivial action on an infinite set
    (`not_isTypeA2_of_trivial`, `not_isTypeA2_unit_nat`).
* `IsTypeParenA2`:
  * `Equiv.Perm (Fin 3)` acting on `Fin 3` is of type (A₂)
    (`isTypeParenA2_perm_fin_three`);
  * the same group acting on a point is of type [A₂] but not (A₂)
    (`isTypeA2_perm_fin_three_unit`, `not_isTypeParenA2_perm_fin_three_unit`), so [A₂]
    does not force faithfulness.
* `actionKernel`:
  * trivial for `Equiv.Perm (Fin 3)` acting on `Fin 3` (`actionKernel_perm_fin_three`);
  * the whole group for a trivial action (`actionKernel_eq_top_of_trivial`).
* The quotient in `Question58` is finitely presented whenever `G` is finite
  (`isFinitelyPresented_quotient_of_finite`), so a witness needs `G` infinite.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation.TypeA2

/-- Every action of a finite group on a finite non-empty set is of type [A₂]. -/
theorem isTypeA2_of_finite (G S : Type) [Group G] [MulAction G S] [Finite G] [Finite S]
    [Nonempty S] : IsTypeA2 G S :=
  ⟨inferInstance, inferInstance,
    fun s => (Group.fg_iff_subgroup_fg (MulAction.stabilizer G s)).mp inferInstance,
    Quotient.finite _⟩

/-- No action on the empty set is of type [A₂]. -/
theorem not_isTypeA2_empty (G : Type) [Group G] [MulAction G Empty] : ¬ IsTypeA2 G Empty :=
  fun h => h.1.elim fun e => e.elim

/-- A trivial action on an infinite set is not of type [A₂]: `G` has infinitely many
orbits on `S × S`. -/
theorem not_isTypeA2_of_trivial (G S : Type) [Group G] [MulAction G S] [Infinite S]
    (htriv : ∀ (g : G) (s : S), g • s = s) : ¬ IsTypeA2 G S := by
  rintro ⟨-, -, -, hfin⟩
  have hinj : Function.Injective (fun p : S × S =>
      (Quotient.mk (MulAction.orbitRel G (S × S)) p : MulAction.orbitRel.Quotient G (S × S))) := by
    intro p q hpq
    have h : p ∈ MulAction.orbit G q := Quotient.exact hpq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
    subst hg
    exact Prod.ext (htriv g q.1) (htriv g q.2)
  have := Finite.of_injective _ hinj
  exact not_finite (S × S)

/-- The trivial action of the one-element group on `ℕ` is not of type [A₂]. -/
theorem not_isTypeA2_unit_nat :
    ¬ @IsTypeA2 Unit ℕ _ (MulAction.compHom ℕ (1 : Unit →* Equiv.Perm ℕ)) :=
  @not_isTypeA2_of_trivial Unit ℕ _ (MulAction.compHom ℕ (1 : Unit →* Equiv.Perm ℕ)) _
    fun _ _ => rfl

/-- The natural action of `Equiv.Perm (Fin 3)` on `Fin 3` is of type (A₂). -/
theorem isTypeParenA2_perm_fin_three : IsTypeParenA2 (Equiv.Perm (Fin 3)) (Fin 3) :=
  ⟨isTypeA2_of_finite _ _, inferInstance⟩

/-- A non-trivial group acting trivially is not of type (A₂). -/
theorem not_isTypeParenA2_of_trivial (G S : Type) [Group G] [MulAction G S] [Nontrivial G]
    (htriv : ∀ (g : G) (s : S), g • s = s) : ¬ IsTypeParenA2 G S := by
  rintro ⟨-, hfaith⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (FaithfulSMul.eq_of_smul_eq_smul (α := S) fun s => by rw [htriv, one_smul])

/-- `Equiv.Perm (Fin 3)` acting on a point is of type [A₂]. -/
theorem isTypeA2_perm_fin_three_unit :
    @IsTypeA2 (Equiv.Perm (Fin 3)) Unit _
      (MulAction.compHom Unit (1 : Equiv.Perm (Fin 3) →* Equiv.Perm Unit)) :=
  @isTypeA2_of_finite (Equiv.Perm (Fin 3)) Unit _
    (MulAction.compHom Unit (1 : Equiv.Perm (Fin 3) →* Equiv.Perm Unit)) _ _ _

/-- `Equiv.Perm (Fin 3)` acting on a point is not of type (A₂). -/
theorem not_isTypeParenA2_perm_fin_three_unit :
    ¬ @IsTypeParenA2 (Equiv.Perm (Fin 3)) Unit _
      (MulAction.compHom Unit (1 : Equiv.Perm (Fin 3) →* Equiv.Perm Unit)) :=
  @not_isTypeParenA2_of_trivial (Equiv.Perm (Fin 3)) Unit _
    (MulAction.compHom Unit (1 : Equiv.Perm (Fin 3) →* Equiv.Perm Unit)) _
    fun _ _ => Subsingleton.elim _ _

/-- The kernel of `Equiv.Perm (Fin 3)` acting on `Fin 3` is trivial. -/
theorem actionKernel_perm_fin_three : actionKernel (Equiv.Perm (Fin 3)) (Fin 3) = ⊥ := by
  ext g
  rw [mem_actionKernel, Subgroup.mem_bot]
  exact ⟨fun h => Equiv.ext h, fun h s => by rw [h, one_smul]⟩

/-- The kernel of a trivial action is the whole group. -/
theorem actionKernel_eq_top_of_trivial (G S : Type) [Group G] [MulAction G S]
    (htriv : ∀ (g : G) (s : S), g • s = s) : actionKernel G S = ⊤ := by
  ext g
  exact ⟨fun _ => Subgroup.mem_top g, fun _ => mem_actionKernel.mpr (htriv g)⟩

/-- When `G` is finite, `G ⧸ ker(G ↷ S)` is finitely presented.  So a witness for
`Question58` needs `G` infinite. -/
theorem isFinitelyPresented_quotient_of_finite (G S : Type) [Group G] [MulAction G S]
    [Finite G] : Group.IsFinitelyPresented (G ⧸ actionKernel G S) :=
  inferInstance

end GroupApproximation.TypeA2
