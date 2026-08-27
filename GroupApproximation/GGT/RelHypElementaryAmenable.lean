import GroupApproximation.GGT.RelHypDefinition
import GroupApproximation.Algebra.AmenableConstructions
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary groups are amenable

`ElementaryAmenableStatement` -- a group with a cyclic subgroup of finite index
carries an invariant mean -- was the fourth and smallest named input of
`GGT/RelHypFournierFacio.lean`.  This module proves it, so it is a named `Prop`
with a proof rather than a citation.

`GGT/RelHypKazhdanNonElementary.lean` removes the need for it along the
Fournier-Facio chain by a different route, so nothing there waits on this file;
what is proved here is the statement itself, which is worth having on its own
and is the standard permanence fact.

## What was already in the repository, and what is new

`Algebra/Amenable.lean` and `Algebra/AmenableMean.lean` carry two towers: the
measure formulation `IsAmenable G = Nonempty (InvariantMean G)` and the mean
formulation `HasInvariantMean G = Nonempty (FunctionMean G)`, with
`isAmenable_of_hasInvariantMean` going one way and nothing going back.  All the
permanence lemmas live in the mean tower, so the proof stays there until the
last line.  Already present, and used here unchanged:

* `hasInvariantMean_int` -- `ℤ` is amenable, by Cesaro averages along an
  ultrafilter (`Algebra/AmenableInt.lean`).  So step (b) of the obvious plan is
  done and needs no Banach limit built by hand.
* `finiteFunctionMean` -- averaging over a finite group.  Step (a), done.
* `hasInvariantMean_of_surjective` -- amenability passes to images.
* `hasInvariantMean_of_extension` -- amenability is closed under extensions,
  by averaging along the cosets of a **normal** subgroup and then over the
  quotient.

Three things are new here, and the third is the only one with content.

* `hasInvariantMean_of_isCyclic` -- **a cyclic group is amenable**: it is a
  surjective image of `ℤ`.  The repository had this only for a subgroup
  `Subgroup.zpowers g` (`hasInvariantMean_zpowers`), not for an abstract cyclic
  group.
* `isCyclic_of_le` -- **a subgroup of a cyclic subgroup is cyclic**, obtained
  by pushing Mathlib's instance for `N.subgroupOf C` along the surjection
  `↥(N.subgroupOf C) → ↥N`.
* `hasInvariantMean_of_finiteIndex_normal` -- **finite-index permanence, normal
  case**: a normal subgroup of finite index carrying an invariant mean gives
  one to the whole group, the quotient being finite.

## Why the normal core, and not a transversal

The extension lemma asks for a normal subgroup, and a finite-index cyclic
subgroup need not be normal.  The repair is `C.normalCore`: it is normal, it is
contained in `C`, and Mathlib already knows it inherits finite index.  Being
inside a cyclic group it is cyclic, hence amenable, and the quotient by it is
finite, hence amenable, so the extension lemma applies to `G` directly.  No
transversal averaging has to be built: the two averaging constructions the
argument needs -- over a finite group and along the cosets of a normal
subgroup -- are both already in `Algebra/AmenableMean.lean`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

/-! ## 1.  Cyclic groups -/

/-- **A cyclic group is amenable.**  It is a surjective image of `ℤ` under
`zpowersHom`, and amenability passes to images. -/
theorem hasInvariantMean_of_isCyclic (A : Type) [Group A] [IsCyclic A] :
    Amenability.HasInvariantMean A := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  refine Amenability.hasInvariantMean_of_surjective (zpowersHom A g) ?_
    Amenability.hasInvariantMean_int
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  exact ⟨Multiplicative.ofAdd n, hn⟩

/-- **A subgroup of a cyclic subgroup is cyclic.**

Mathlib gives `IsCyclic ↥(N.subgroupOf C)` from `IsCyclic ↥C`; the forgetful map
to `↥N` is a surjective homomorphism, and cyclicity passes to images. -/
theorem isCyclic_of_le {G : Type} [Group G] {N C : Subgroup G} (hNC : N ≤ C)
    [IsCyclic ↥C] : IsCyclic ↥N := by
  let f : ↥(N.subgroupOf C) →* ↥N :=
    { toFun := fun x => ⟨((x : ↥C) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    exact ⟨⟨⟨y, hNC hy⟩, hy⟩, rfl⟩
  exact isCyclic_of_surjective f hf

/-! ## 2.  Finite-index permanence, normal case -/

/-- **A normal subgroup of finite index carrying an invariant mean gives one to
the whole group.**  The quotient is finite, hence amenable, and the extension
lemma of `Algebra/AmenableMean.lean` does the rest. -/
theorem hasInvariantMean_of_finiteIndex_normal {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] [N.FiniteIndex]
    (hN : Amenability.HasInvariantMean ↥N) : Amenability.HasInvariantMean G := by
  classical
  haveI : Finite (G ⧸ N) := N.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  exact Amenability.hasInvariantMean_of_extension N hN
    ⟨Amenability.finiteFunctionMean (G ⧸ N)⟩

/-! ## 3.  The statement -/

/-- **An elementary group is amenable.**  Pass to the normal core of the
finite-index cyclic subgroup: it is normal, of finite index, and cyclic, so it
is amenable and the quotient by it is finite. -/
theorem hasInvariantMean_of_isElementaryGroup {G : Type} [Group G]
    (h : IsElementaryGroup G) : Amenability.HasInvariantMean G := by
  obtain ⟨C, hfi, hcyc⟩ := h
  haveI := hfi
  haveI := hcyc
  haveI : (C.normalCore).FiniteIndex := inferInstance
  haveI : IsCyclic ↥(C.normalCore) := isCyclic_of_le C.normalCore_le
  exact hasInvariantMean_of_finiteIndex_normal C.normalCore
    (hasInvariantMean_of_isCyclic ↥(C.normalCore))

/-- **An elementary group is amenable**, in the measure formulation. -/
theorem isAmenable_of_isElementaryGroup {G : Type} [Group G]
    (h : IsElementaryGroup G) : Amenability.IsAmenable G :=
  Amenability.isAmenable_of_hasInvariantMean (hasInvariantMean_of_isElementaryGroup h)

/-- **`ElementaryAmenableStatement`, proved.**  The fourth named input of
`GGT/RelHypFournierFacio.lean` is a theorem. -/
theorem elementaryAmenableStatement : ElementaryAmenableStatement :=
  fun _ _ h => isAmenable_of_isElementaryGroup h

end RelHyp
end GGT
end GroupApproximation
