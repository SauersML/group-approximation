/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Defs
import GroupApproximation.TypeA2.Statement
import GroupApproximation.TypeA2.Answer

/-!
# Fournier-Facio–Wu–Zaremsky Question 5.8: solution

This is the solution half of the Palomar pair `Palomar/TypeA2Challenge.lean` /
`Palomar/TypeA2Solution.lean`, configuration `Palomar/comparator-type-a2.json`.

The module repeats the Challenge's shared block byte for byte.  The development module
`GroupApproximation.TypeA2.Statement` gives the same two definitions the same bodies
under `GroupApproximation.TypeA2`, so the bridges hold by `rfl`:
* `isTypeA2_iff`: `FFWZ.IsTypeA2 G S ↔ GroupApproximation.TypeA2.IsTypeA2 G S`;
* `actionKernel_eq`: `FFWZ.actionKernel G S = GroupApproximation.TypeA2.actionKernel G S`;
* `exists_isTypeA2_quotient_not_isFinitelyPresented_of`: the development's `Question58`
  gives the Challenge statement.

The Challenge theorem `exists_isTypeA2_quotient_not_isFinitelyPresented` applies the last
bridge to `GroupApproximation.TypeA2.question58` from `GroupApproximation.TypeA2.Answer`.
That module builds the witness from Thompson's group `F` acting on the positive dyadic
rationals.

The prose of this module was written by Claude (Anthropic).
-/

namespace FFWZ

-- BEGIN SHARED BLOCK (kept byte-identical in `Palomar/TypeA2Challenge.lean` and `Palomar/TypeA2Solution.lean`)

/-- An action of `G` on `S` of **type [A₂]** (FFWZ Definition 1.3, `n = 2`): `S` is
non-empty, `G` is finitely presented, every point stabilizer is finitely generated,
and the diagonal action of `G` on `S × S` has finitely many orbits.  The action need
not be faithful. -/
def IsTypeA2 (G S : Type) [Group G] [MulAction G S] : Prop :=
  Nonempty S ∧ Group.IsFinitelyPresented G ∧ (∀ s : S, (MulAction.stabilizer G s).FG) ∧
    Finite (MulAction.orbitRel.Quotient G (S × S))

/-- The kernel `ker(G ↷ S)` of an action: the kernel of `G →* Equiv.Perm S`, that is,
the elements of `G` that fix every point of `S`. -/
abbrev actionKernel (G S : Type) [Group G] [MulAction G S] : Subgroup G :=
  (MulAction.toPermHom G S).ker

-- END SHARED BLOCK

/-- The Challenge's `IsTypeA2` is the development's `GroupApproximation.TypeA2.IsTypeA2`. -/
theorem isTypeA2_iff {G S : Type} [Group G] [MulAction G S] :
    IsTypeA2 G S ↔ GroupApproximation.TypeA2.IsTypeA2 G S :=
  Iff.rfl

/-- The Challenge's `actionKernel` is the development's
`GroupApproximation.TypeA2.actionKernel`. -/
theorem actionKernel_eq {G S : Type} [Group G] [MulAction G S] :
    actionKernel G S = GroupApproximation.TypeA2.actionKernel G S :=
  rfl

/-- The development's `GroupApproximation.TypeA2.Question58` gives the Challenge
statement: some group action `G ↷ S` of type [A₂] has a quotient `G ⧸ ker(G ↷ S)` that
is not finitely presented. -/
theorem exists_isTypeA2_quotient_not_isFinitelyPresented_of
    (h : GroupApproximation.TypeA2.Question58) :
    ∃ (G : Type) (_ : Group G) (S : Type) (_ : MulAction G S),
      IsTypeA2 G S ∧ ¬ Group.IsFinitelyPresented (G ⧸ actionKernel G S) :=
  h

/-- **Question 5.8 has a positive answer**: some group action `G ↷ S` of type [A₂]
has a quotient `G ⧸ ker(G ↷ S)` that is not finitely presented. -/
theorem exists_isTypeA2_quotient_not_isFinitelyPresented :
    ∃ (G : Type) (_ : Group G) (S : Type) (_ : MulAction G S),
      IsTypeA2 G S ∧ ¬ Group.IsFinitelyPresented (G ⧸ actionKernel G S) :=
  exists_isTypeA2_quotient_not_isFinitelyPresented_of GroupApproximation.TypeA2.question58

end FFWZ
