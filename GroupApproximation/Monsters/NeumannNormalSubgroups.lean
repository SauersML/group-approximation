import GroupApproximation.Monsters.NeumannContinuum
import GroupApproximation.Sofic.ContinuumFromNormalSubgroups
import Mathlib.Data.Finite.Sum

/-!
# One finitely generated group with continuum many normal subgroups

`Sofic/ContinuumFromNormalSubgroups` reduces the continuum-family obligation
behind the manuscript's multiplicity paragraph to a single sentence about a
single group:

> **some** finitely generated group has `2^{\aleph_0}` normal subgroups.

That reduction is sharp and it is short --- a normal subgroup with a prescribed
quotient is the kernel of an epimorphism, an epimorphism out of a finitely
generated group is pinned down by finitely many values, so the map "normal
subgroup ↦ isomorphism type of the quotient" has countable fibres and a
continuum-sized domain forces a continuum-sized image --- but at the revision
where it was written nothing in the corpus exhibited such a group, so the
reduction reduced to nothing.  This file exhibits one.

## The group

`Monsters/NeumannAlternatingFamily` builds, for every `S ⊆ ℕ`, the finitely
generated group

  `NeumannGroup S = A₅ ≀_{F₂ / markedSubgroup S} F₂`,

and `Monsters/NeumannContinuum` extracts from that family a continuum-sized
transversal of the isomorphism relation.  The observation here is that
`fg_wreathQuotient` generates *every* member of the family by the **same finite
set of markers**: the two free generators of `F₂`, and the sixty one-site lamps
at the base coset, one for each element of `A₅`.  So writing

  `Marker = Fin 2 ⊕ A₅`,  `FixedFree = FreeGroup Marker`,

there is, for every subgroup `H ≤ F₂`, a *surjective* homomorphism
`genHom H : FixedFree ↠ A₅ ≀_{F₂/H} F₂` --- one fixed finitely generated group
mapping onto the whole family.

The rest is bookkeeping.  Distinct members of the transversal are nonisomorphic,
so their kernels in `FixedFree` are distinct; the transversal has size
`2^{\aleph_0}`; and `FixedFree` is countable, so it has at most `2^{\aleph_0}`
subgroups at all.  Hence

  `#{N ⊴ FixedFree} = 2^{\aleph_0}`,

which is `continuum_normalSubgroups`, and it is exactly the hypothesis
`ContinuumFromNormalSubgroups.exists_continuum_pairwise_nonisomorphic_quotients`
consumes.

## Why bother, given `Monsters/NeumannContinuum`

`NeumannContinuum.manuscriptContinuumMultiplicityUnconditional` already
discharges the manuscript's hypothesis, by separating the family with the
counting argument applied to the subgroups `markedSubgroup S` directly.  This
file is a second packaging of the same construction through a different
invariant --- the normal subgroups of one fixed group rather than a family of
coset spaces --- and it is what makes `Sofic/ContinuumFromNormalSubgroups` a
statement about an existing object rather than a reduction with no instance.
It also isolates the cheapest form of the classical fact: *a* finitely generated
group with continuum many normal subgroups, no isomorphism types mentioned.

## What is not claimed

Neumann's own groups are two-generator.  The groups here are finitely generated
with a sixty-two element marker set, and `FixedFree` is free of rank sixty-two;
no attempt is made to compute the minimal number of generators of anything.  The
manuscript's deduction never uses two-generation, and the Lean statements it
consumes take `Group.FG`.
-/

namespace GroupApproximation
namespace NeumannNormalSubgroups

open NeumannFamily SemidirectProduct ChosenMarkedPresentation

/-! ## A single finitely generated free group covering the whole family -/

/-- The marker type of the uniform generating set: two markers for the free
generators of `F₂`, and one marker for each value of the lamp group `A₅`. -/
abbrev Marker : Type := Fin 2 ⊕ AltLamp

/-- The free group on the markers.  Every member of the alternating lamp family
is a quotient of this one group. -/
abbrev FixedFree : Type := FreeGroup Marker

/-- `FixedFree` is finitely generated: the markers form a finite set and they
generate. -/
instance instFGFixedFree : Group.FG FixedFree :=
  Group.fg_iff.mpr
    ⟨Set.range (FreeGroup.of : Marker → FixedFree), FreeGroup.closure_range_of Marker,
      Set.finite_range _⟩

/-- `FixedFree` is countable, being finitely generated. -/
theorem countable_fixedFree : Countable FixedFree :=
  ContinuumMultiplicity.countable_of_fg FixedFree

/-! ## The uniform marking of the family

For each subgroup `H ≤ F₂` the markers are interpreted in
`A₅ ≀_{F₂/H} F₂`: the two `Fin 2` markers as the free generators, sitting in the
acting factor, and the `A₅` markers as the one-site lamps at the base coset.
`wreath_eq_closure` says that these interpretations generate, because the action
of `F₂` on `F₂/H` is transitive.
-/

/-- The interpretation of the markers inside `A₅ ≀_{F₂/H} F₂`. -/
def genMap (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] :
    Marker → Wreath AltLamp Acting (Acting ⧸ H) :=
  Sum.elim (fun i : Fin 2 => (inr (FreeGroup.of i) : Wreath AltLamp Acting (Acting ⧸ H)))
    (fun l : AltLamp =>
      (inl (Lamp.single (baseSite H) l) : Wreath AltLamp Acting (Acting ⧸ H)))

/-- The homomorphism out of `FixedFree` determined by the markers. -/
def genHom (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] :
    FixedFree →* Wreath AltLamp Acting (Acting ⧸ H) :=
  FreeGroup.lift (genMap H)

theorem genHom_def (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] :
    genHom H = FreeGroup.lift (genMap H) := rfl

/-- The markers are interpreted onto exactly the generating set of
`wreath_eq_closure`: the free generators in the acting factor, together with the
one-site lamps at the base coset. -/
theorem range_genMap (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] :
    Set.range (genMap H) =
      ((inr : Acting →* Wreath AltLamp Acting (Acting ⧸ H)) ''
          Set.range (FreeGroup.of : Fin 2 → Acting)) ∪
        ((fun l : AltLamp =>
            (inl (Lamp.single (baseSite H) l) : Wreath AltLamp Acting (Acting ⧸ H))) ''
          (Set.univ : Set AltLamp)) := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl i => exact Or.inl ⟨FreeGroup.of i, ⟨i, rfl⟩, rfl⟩
    | inr l => exact Or.inr ⟨l, Set.mem_univ l, rfl⟩
  · rintro (⟨g, ⟨i, rfl⟩, rfl⟩ | ⟨l, -, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr l, rfl⟩

/-- **One group maps onto the whole family.**  For every subgroup `H ≤ F₂` the
marker homomorphism `FixedFree → A₅ ≀_{F₂/H} F₂` is surjective.  The source does
not depend on `H`; only the interpretation of the markers does. -/
theorem surjective_genHom (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] :
    Function.Surjective (genHom H) := by
  have htrans : ∀ x : Acting ⧸ H, ∃ g : Acting, g • baseSite H = x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, smul_baseSite H g⟩
  have hclosure := wreath_eq_closure (K := AltLamp) (G := Acting) (X := Acting ⧸ H)
    (baseSite H) htrans (SG := Set.range (FreeGroup.of : Fin 2 → Acting))
    (FreeGroup.closure_range_of (Fin 2)) (SK := (Set.univ : Set AltLamp))
    Subgroup.closure_univ
  refine MonoidHom.range_eq_top.mp ?_
  rw [genHom_def, FreeGroup.range_lift_eq_closure, range_genMap]
  exact hclosure

/-- Each member of the family is the quotient of `FixedFree` by the kernel of its
marker homomorphism. -/
theorem mulEquiv_quotient_ker (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] :
    Nonempty (FixedFree ⧸ (genHom H).ker ≃* Wreath AltLamp Acting (Acting ⧸ H)) :=
  ⟨QuotientGroup.quotientKerEquivOfSurjective (genHom H) (surjective_genHom H)⟩

/-! ## Continuum many normal subgroups -/

/-- **A finitely generated group with continuum many normal subgroups.**

The lower bound is the alternating lamp family: distinct members of
`NeumannContinuum.transversal` give nonisomorphic groups, hence distinct kernels
in `FixedFree`, and the transversal has size `2^{\aleph_0}`.  The upper bound is
countability: `FixedFree` is finitely generated, hence countable, so it has at
most `2^{\aleph_0}` subsets and a fortiori at most that many normal subgroups.

This is the whole remaining obligation of
`Sofic/ContinuumFromNormalSubgroups`. -/
theorem continuum_normalSubgroups :
    Cardinal.mk (ContinuumFromNormalSubgroups.NormalSubgroups FixedFree)
      = Cardinal.continuum := by
  classical
  haveI : Countable FixedFree := countable_fixedFree
  refine le_antisymm ?_ ?_
  · calc Cardinal.mk (ContinuumFromNormalSubgroups.NormalSubgroups FixedFree)
        ≤ Cardinal.mk (Subgroup FixedFree) :=
          Cardinal.mk_subtype_le (fun N : Subgroup FixedFree => N.Normal)
      _ ≤ Cardinal.mk (Set FixedFree) :=
          Cardinal.mk_le_of_injective SetLike.coe_injective
      _ = 2 ^ Cardinal.mk FixedFree := Cardinal.mk_set
      _ ≤ 2 ^ Cardinal.aleph0 :=
          Cardinal.power_le_power_left two_ne_zero Cardinal.mk_le_aleph0
      _ = Cardinal.continuum := Cardinal.two_power_aleph0
  · rw [← NeumannContinuum.mk_neumannIndex]
    refine Cardinal.mk_le_of_injective
      (f := fun i : NeumannContinuum.NeumannIndex =>
        (⟨(genHom (markedSubgroup (i : Set ℕ))).ker, inferInstance⟩ :
          ContinuumFromNormalSubgroups.NormalSubgroups FixedFree)) ?_
    intro i j hij
    have hker : (genHom (markedSubgroup (i : Set ℕ))).ker
        = (genHom (markedSubgroup (j : Set ℕ))).ker := congrArg Subtype.val hij
    have e : NeumannGroup (i : Set ℕ) ≃* NeumannGroup (j : Set ℕ) :=
      (QuotientGroup.quotientKerEquivOfSurjective
          (genHom (markedSubgroup (i : Set ℕ))) (surjective_genHom _)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          (QuotientGroup.quotientKerEquivOfSurjective
            (genHom (markedSubgroup (j : Set ℕ))) (surjective_genHom _)))
    exact Subtype.ext
      (NeumannContinuum.transversal_pairwise (i : Set ℕ) i.2 (j : Set ℕ) j.2 ⟨e⟩)

/-- **The reduction of `Sofic/ContinuumFromNormalSubgroups`, instantiated.**
Continuum many normal subgroups of one finitely generated group yield continuum
many pairwise nonisomorphic quotients of it, by the countable-fibres argument of
that file. -/
theorem exists_continuum_pairwise_nonisomorphic_quotients :
    ∃ J : Set (ContinuumFromNormalSubgroups.NormalSubgroups FixedFree),
      Cardinal.mk J = Cardinal.continuum ∧
      ∀ N ∈ J, ∀ M ∈ J,
        Nonempty (ContinuumFromNormalSubgroups.Quot N ≃*
          ContinuumFromNormalSubgroups.Quot M) → N = M :=
  ContinuumFromNormalSubgroups.exists_continuum_pairwise_nonisomorphic_quotients
    FixedFree continuum_normalSubgroups

/-! ## The manuscript's family, indexed by normal subgroups -/

/-- A continuum-sized set of normal subgroups of `FixedFree` with pairwise
nonisomorphic quotients. -/
noncomputable def quotientTransversal :
    Set (ContinuumFromNormalSubgroups.NormalSubgroups FixedFree) :=
  exists_continuum_pairwise_nonisomorphic_quotients.choose

theorem mk_quotientTransversal :
    Cardinal.mk quotientTransversal = Cardinal.continuum :=
  exists_continuum_pairwise_nonisomorphic_quotients.choose_spec.1

theorem quotientTransversal_pairwise :
    ∀ N ∈ quotientTransversal, ∀ M ∈ quotientTransversal,
      Nonempty (ContinuumFromNormalSubgroups.Quot N ≃*
        ContinuumFromNormalSubgroups.Quot M) → N = M :=
  exists_continuum_pairwise_nonisomorphic_quotients.choose_spec.2

/-- The index type of the family: a continuum of normal subgroups of one fixed
finitely generated group. -/
noncomputable abbrev QuotientIndex : Type := ↥quotientTransversal

/-- The family itself: the quotients of `FixedFree` along the transversal. -/
noncomputable abbrev QuotientFamily (i : QuotientIndex) : Type :=
  ContinuumFromNormalSubgroups.Quot
    (i : ContinuumFromNormalSubgroups.NormalSubgroups FixedFree)

theorem mk_quotientIndex : Cardinal.mk QuotientIndex = Cardinal.continuum :=
  mk_quotientTransversal

/-- **The family is pairwise nonisomorphic.** -/
theorem quotientFamily_pairwise (i j : QuotientIndex) :
    Nonempty (QuotientFamily i ≃* QuotientFamily j) → i = j := fun h =>
  Subtype.ext (quotientTransversal_pairwise _ i.2 _ j.2 h)

/-- **Neumann's statement, in the strength the manuscript uses, through normal
subgroups.**  There is a continuum of pairwise nonisomorphic finitely generated
groups: the quotients of a single finitely generated free group by a continuum
of its normal subgroups. -/
theorem neumann_continuum_through_normal_subgroups :
    Cardinal.mk QuotientIndex = Cardinal.continuum ∧
      (∀ i : QuotientIndex, Group.FG (QuotientFamily i)) ∧
      ∀ i j : QuotientIndex, Nonempty (QuotientFamily i ≃* QuotientFamily j) → i = j :=
  ⟨mk_quotientIndex, fun _ => inferInstance, quotientFamily_pairwise⟩

/-- **Continuum multiplicity, unconditionally, through normal subgroups.**  The
manuscript's counting step `ContinuumMultiplicity.manuscriptContinuumMultiplicity`
applied to the family built here: a continuum of pairwise nonisomorphic finitely
generated groups, each of them not operator-MF after multiplying by `E`.

This is the same conclusion as
`NeumannContinuum.manuscriptContinuumMultiplicityUnconditional`, reached through
`Sofic/ContinuumFromNormalSubgroups` rather than around it. -/
theorem manuscriptContinuumMultiplicityViaNormalSubgroups :
    ∃ J : Set QuotientIndex, Cardinal.mk J = Cardinal.continuum ∧
      (∀ i ∈ J, Group.FG (MarkedGroup × QuotientFamily i) ∧
        ¬ IsOperatorMF (MarkedGroup × QuotientFamily i)) ∧
      ∀ i ∈ J, ∀ j ∈ J,
        Nonempty ((MarkedGroup × QuotientFamily i) ≃*
          (MarkedGroup × QuotientFamily j)) → i = j :=
  ContinuumMultiplicity.manuscriptContinuumMultiplicity QuotientFamily
    quotientFamily_pairwise mk_quotientIndex

end NeumannNormalSubgroups
end GroupApproximation
