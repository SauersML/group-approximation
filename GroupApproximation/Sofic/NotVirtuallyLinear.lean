import GroupApproximation.Algebra.MalcevLinear
import GroupApproximation.Sofic.LEFSofic
import Mathlib.GroupTheory.Schreier

/-!
# Not linear, and not even virtually linear

Corollaries 46.4 and 46.6 of the dossier.  Corollary 46.4 -- a finitely
generated group with nontrivial finite residual has no faithful
finite-dimensional linear representation over any field -- follows directly from
Mal'cev.  Corollary 46.6 strengthens it: no *finite-index subgroup* has one
either, so the examples are not virtually linear.

The strengthening is not cosmetic.  Non-linearity of a group says nothing about
its finite-index subgroups in general, and "virtually linear" is the property
that actually rules out the standard constructions.  Two inputs make it work,
and both are already in the repository or in Mathlib:

* **Schreier** (`Subgroup.fg_of_index_ne_zero`): a finite-index subgroup of a
  finitely generated group is finitely generated -- so Mal'cev applies to the
  subgroup, which is what the hypothesis of `MalcevLinear` needs;
* **residual finiteness climbs finite index**
  (`residuallyFinite_of_finiteIndex`, in `Sofic/LEFSofic`, which is Lemma 46.5): a group
  with a residually finite finite-index subgroup is residually finite.

Together: a faithful linear representation of a finite-index subgroup `H` makes
`H` residually finite by Mal'cev, hence makes the whole group residually finite,
contradicting the hypothesis.  So the two lemmas do all the work and the
corollary is their composition.

Stated for an arbitrary field and dimension, and for the group-theoretic
hypothesis "not residually finite" rather than for any particular construction,
so it applies to every witness in the development at once -- the concrete
`W_K`, the alternating-lamp family, and the explicit mod-two group -- as soon as
each is known to have nontrivial finite residual.

## What is not claimed

Nothing here produces the non-residual-finiteness; it is the hypothesis.  And
nothing here says the group has no *infinite-dimensional* linear
representations, nor that it fails to embed in a linear group of some other
kind; the statement is about finite-dimensional representations over fields,
which is exactly the class Mal'cev controls.
-/

namespace GroupApproximation

namespace NotVirtuallyLinear

open Matrix

universe u v

/-- **Corollary 46.4.**  A finitely generated group that is not residually
finite has no faithful finite-dimensional linear representation over any
field.  This is Mal'cev, restated without the matrix bookkeeping. -/
theorem not_injective_of_not_residuallyFinite {G : Type u} [Group G]
    [Group.FG G] (hG : ¬ Group.ResiduallyFinite G)
    {F : Type v} [Field F] {d : ℕ}
    (ρ : G →* GeneralLinearGroup (Fin d) F) :
    ¬ Function.Injective ρ :=
  MalcevLinear.not_injective_of_not_residuallyFinite hG ρ

/-- A faithful finite-dimensional representation makes a finitely generated
group residually finite: the contrapositive of Mal'cev, in the direction the
virtual statement consumes. -/
theorem residuallyFinite_of_injective {G : Type u} [Group G] [Group.FG G]
    {F : Type v} [Field F] {d : ℕ}
    (ρ : G →* GeneralLinearGroup (Fin d) F) (hρ : Function.Injective ρ) :
    Group.ResiduallyFinite G := by
  by_contra hcon
  exact MalcevLinear.not_injective_of_not_residuallyFinite hcon ρ hρ

/-- **Corollary 46.6.**  A finitely generated group that is not residually
finite is not *virtually* linear: no finite-index subgroup admits a faithful
finite-dimensional representation over any field.

Schreier makes the subgroup finitely generated, Mal'cev makes it residually
finite, and residual finiteness climbs back up the finite index -- contradicting
the hypothesis. -/
theorem not_injective_of_finiteIndex {G : Type u} [Group G] [Group.FG G]
    (hG : ¬ Group.ResiduallyFinite G)
    (H : Subgroup G) [H.FiniteIndex]
    {F : Type v} [Field F] {d : ℕ}
    (ρ : H →* GeneralLinearGroup (Fin d) F) :
    ¬ Function.Injective ρ := by
  intro hinj
  haveI : Group.FG H := inferInstance
  haveI : Group.ResiduallyFinite H := residuallyFinite_of_injective ρ hinj
  exact hG (residuallyFinite_of_finiteIndex H)

end NotVirtuallyLinear

end GroupApproximation
