import GroupApproximation.Sofic.SoficActionFiniteOrbits
import Mathlib.GroupTheory.Index

/-!
# Basic sofic actions

Two immediate consequences of the exact finite-orbit model of
`Sofic.SoficActionFiniteOrbits`.

* `isSoficAction_of_finite` — every action on a finite set is sofic.
* `isSoficAction_quotient_of_finite` — the coset action on a finite-index
  quotient is sofic, with zero multiplicativity error and no bad model points.
  This is Lemma 30.2 of the dossier, the base case of the Chabauty argument
  which upgrades finite-index separability to soficity of arbitrary transitive
  actions.
-/

namespace GroupApproximation

universe u v

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- Every action on a finite set is sofic, with exact models. -/
theorem isSoficAction_of_finite [Finite X] [DecidableEq X] :
    IsSoficAction G X :=
  isSoficAction_of_finite_orbits fun _ => Set.toFinite _

/-- **Lemma 30.2.**  The coset action of a group on a finite quotient is sofic,
with zero multiplicativity error and no bad model points. -/
theorem isSoficAction_quotient_of_finite (K : Subgroup G) [Finite (G ⧸ K)]
    [DecidableEq (G ⧸ K)] : IsSoficAction G (G ⧸ K) :=
  isSoficAction_of_finite

/-- The finite-index form of Lemma 30.2. -/
theorem isSoficAction_quotient_of_finiteIndex (K : Subgroup G) [K.FiniteIndex]
    [DecidableEq (G ⧸ K)] : IsSoficAction G (G ⧸ K) := by
  haveI : Finite (G ⧸ K) := K.finite_quotient_of_finiteIndex
  exact isSoficAction_quotient_of_finite K

end GroupApproximation
