import GroupApproximation.Sofic.ContinuumFamilyCriterion

/-!
# Continuum multiplicity from normal subgroups alone

`Sofic.ContinuumFamilyCriterion` reduced the manuscript's continuum-family
obligation to: a family of finitely generated groups with an isomorphism
invariant recovering the index.  Producing such an invariant is the hard half
of Neumann's theorem --- his is the set of alternating groups occurring as
minimal normal subgroups, and establishing it needs the two-generation of
`Aₙ` by a 3-cycle and an n-cycle together with a support-separation argument.

This file removes that half.  The observation is a counting one, in the same
spirit as the counting step already in `Sofic.ContinuumMultiplicityCore`:

> A normal subgroup of `Γ` with a *prescribed* quotient is the kernel of an
> epimorphism out of `Γ`.  An epimorphism out of a finitely generated group is
> determined by its values on a finite generating set.  So for a fixed
> quotient there are at most countably many such normal subgroups.

Hence the map "normal subgroup ↦ isomorphism type of the quotient" has
countable fibres, and a continuum-sized domain forces a continuum-sized image.
No invariant has to be exhibited, and nothing about the groups involved has to
be computed.

## What this buys

The obligation behind the manuscript's continuum sentence becomes

> **some** finitely generated group has continuum many normal subgroups

which is strictly weaker than Neumann's theorem and does not mention
isomorphism types at all.  Neumann's family witnesses it, but so does any
finitely generated group with `2^{ℵ₀}` normal subgroups, and the statement is
now about a single group rather than about a family and its invariants.
-/

namespace GroupApproximation
namespace ContinuumFromNormalSubgroups

open ContinuumMultiplicity

/-! ## Quotients indexed by normal subgroups -/

/-- The normal subgroups of `Γ`, as an index type. -/
abbrev NormalSubgroups (Γ : Type) [Group Γ] : Type := {N : Subgroup Γ // N.Normal}

instance normalSubgroups_normal {Γ : Type} [Group Γ] (N : NormalSubgroups Γ) :
    (N : Subgroup Γ).Normal := N.2

/-- The quotient named by a normal subgroup. -/
abbrev Quot {Γ : Type} [Group Γ] (N : NormalSubgroups Γ) : Type :=
  Γ ⧸ (N : Subgroup Γ)

instance quot_fg {Γ : Type} [Group Γ] [Group.FG Γ] (N : NormalSubgroups Γ) :
    Group.FG (Quot N) :=
  Group.fg_of_surjective (QuotientGroup.mk'_surjective (N : Subgroup Γ))

/-- The kernel of an epimorphism realized as "quotient, then an isomorphism"
is the normal subgroup one started from. -/
theorem ker_comp_equiv {Γ G : Type} [Group Γ] [Group G] (N : Subgroup Γ)
    [N.Normal] (e : (Γ ⧸ N) ≃* G) :
    (e.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

/-! ## The counting step -/

/-- **Countably many normal subgroups per isomorphism type.**  This is the
whole content of the reduction: fix a group `G`; a normal subgroup `N` with
`Γ ⧸ N ≅ G` determines, and is determined by, an epimorphism `Γ ↠ G`, and such
an epimorphism is pinned down by finitely many values. -/
theorem countable_iso_class {Γ : Type} [Group Γ] [Group.FG Γ]
    (G : Type) [Group G] :
    {N : NormalSubgroups Γ | Nonempty (Quot N ≃* G)}.Countable := by
  classical
  rcases Set.eq_empty_or_nonempty
      {N : NormalSubgroups Γ | Nonempty (Quot N ≃* G)} with hempty | ⟨N₀, hN₀⟩
  · rw [hempty]
    exact Set.countable_empty
  -- `G` is countable, being isomorphic to a quotient of a finitely generated
  -- (hence countable) group.
  obtain ⟨e₀⟩ := hN₀
  haveI : Countable Γ := ContinuumMultiplicity.countable_of_fg Γ
  haveI : Countable (Quot N₀) :=
    (QuotientGroup.mk'_surjective (N₀ : Subgroup Γ)).countable
  haveI : Countable G := e₀.symm.injective.countable
  -- a finite generating set
  obtain ⟨S, hSgen, hSfin⟩ := Group.fg_iff.mp ‹Group.FG Γ›
  haveI : Finite S := hSfin.to_subtype
  -- choose a realizing isomorphism for each member of the class
  have e : ∀ N : {N : NormalSubgroups Γ | Nonempty (Quot N ≃* G)},
      Quot (N : NormalSubgroups Γ) ≃* G := fun N ↦ Classical.choice N.2
  -- tabulate each member by the values of its epimorphism on the generators
  have hinj : Function.Injective
      (fun (N : {N : NormalSubgroups Γ | Nonempty (Quot N ≃* G)}) (s : S) ↦
        e N (QuotientGroup.mk (s : Γ))) := by
    intro N M hNM
    have hEq :
        (e N).toMonoidHom.comp
            (QuotientGroup.mk' ((N : NormalSubgroups Γ) : Subgroup Γ)) =
          (e M).toMonoidHom.comp
            (QuotientGroup.mk' ((M : NormalSubgroups Γ) : Subgroup Γ)) := by
      refine MonoidHom.eq_of_eqOn_dense hSgen ?_
      intro x hx
      exact congrFun hNM ⟨x, hx⟩
    have hker := congrArg MonoidHom.ker hEq
    rw [ker_comp_equiv, ker_comp_equiv] at hker
    exact Subtype.ext (Subtype.ext hker)
  exact Set.countable_coe_iff.mp hinj.countable

/-! ## The transversal -/

/-- **A continuum-sized index whose isomorphism classes are countable carries
a continuum-sized pairwise nonisomorphic transversal.**  This is the counting
argument of `Sofic.ContinuumMultiplicityCore`, stated for an arbitrary family
rather than for the products with `E`. -/
theorem exists_continuum_transversal {ι : Type} (M : ι → Type) [∀ i, Group (M i)]
    (hclass : ∀ i : ι, {j : ι | Nonempty (M i ≃* M j)}.Countable)
    (hcard : Cardinal.mk ι = Cardinal.continuum) :
    ∃ J : Set ι, Cardinal.mk J = Cardinal.continuum ∧
      ∀ i ∈ J, ∀ j ∈ J, Nonempty (M i ≃* M j) → i = j := by
  classical
  let s : Setoid ι :=
    { r := fun i j ↦ Nonempty (M i ≃* M j)
      iseqv :=
        { refl := fun _ ↦ ⟨MulEquiv.refl _⟩
          symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
          trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩ } }
  have hcl : ∀ q : Quotient s, {i : ι | Quotient.mk s i = q}.Countable := by
    intro q
    have hEq : {i : ι | Quotient.mk s i = q} =
        {i : ι | Nonempty (M q.out ≃* M i)} := by
      ext i
      constructor
      · intro hi
        exact Quotient.exact ((Quotient.out_eq q).trans hi.symm)
      · intro hi
        exact ((Quotient.sound hi).symm).trans (Quotient.out_eq q)
    rw [hEq]
    exact hclass q.out
  haveI hcq : ∀ q : Quotient s, Countable {i : ι | Quotient.mk s i = q} :=
    fun q ↦ (hcl q).to_subtype
  have huniv : (Set.univ : Set ι) =
      ⋃ q : Quotient s, {i : ι | Quotient.mk s i = q} := by
    ext i
    simp
  have hle : Cardinal.mk ι ≤ Cardinal.mk (Quotient s) * Cardinal.aleph0 := by
    have h1 : Cardinal.mk ι =
        Cardinal.mk (⋃ q : Quotient s, {i : ι | Quotient.mk s i = q}) := by
      rw [← huniv, Cardinal.mk_univ]
    rw [h1]
    refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
    refine (Cardinal.sum_le_sum _ (fun _ ↦ Cardinal.aleph0) fun q ↦ ?_).trans ?_
    · exact Cardinal.mk_le_aleph0_iff.mpr (hcq q)
    · rw [Cardinal.sum_const']
  have hQle : Cardinal.mk (Quotient s) ≤ Cardinal.continuum := by
    rw [← hcard]
    exact Cardinal.mk_le_of_surjective Quotient.mk_surjective
  have hQinf : Cardinal.aleph0 < Cardinal.mk (Quotient s) := by
    by_contra hcon
    have hcon' : Cardinal.mk (Quotient s) ≤ Cardinal.aleph0 := not_lt.mp hcon
    have hsmall : Cardinal.mk ι ≤ Cardinal.aleph0 := by
      refine hle.trans ?_
      calc Cardinal.mk (Quotient s) * Cardinal.aleph0
          ≤ Cardinal.aleph0 * Cardinal.aleph0 := by gcongr
        _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0
    rw [hcard] at hsmall
    exact absurd (hsmall.trans_lt Cardinal.aleph0_lt_continuum) (lt_irrefl _)
  have hQeq : Cardinal.mk (Quotient s) = Cardinal.continuum := by
    refine le_antisymm hQle ?_
    have hmax : Cardinal.mk (Quotient s) * Cardinal.aleph0 =
        Cardinal.mk (Quotient s) := by
      rw [Cardinal.mul_eq_max hQinf.le le_rfl, max_eq_left hQinf.le]
    rw [← hcard]
    exact hle.trans hmax.le
  refine ⟨Set.range (Quotient.out : Quotient s → ι), ?_, ?_⟩
  · rw [Cardinal.mk_range_eq _ Quotient.out_injective]
    exact hQeq
  · rintro i ⟨q, rfl⟩ j ⟨p, rfl⟩ he
    have hq : Quotient.mk s q.out = Quotient.mk s p.out := Quotient.sound he
    rw [Quotient.out_eq, Quotient.out_eq] at hq
    rw [hq]

/-! ## The reduction -/

/-- **Neumann's hypothesis, from one group with continuum many normal
subgroups.**  No invariant is exhibited and no isomorphism type is computed:
the quotients along a transversal of the isomorphism relation are
automatically pairwise nonisomorphic, and countability of the fibres is what
keeps the transversal continuum-sized. -/
theorem exists_continuum_pairwise_nonisomorphic_quotients
    (Γ : Type) [Group Γ] [Group.FG Γ]
    (hΓ : Cardinal.mk (NormalSubgroups Γ) = Cardinal.continuum) :
    ∃ J : Set (NormalSubgroups Γ), Cardinal.mk J = Cardinal.continuum ∧
      ∀ N ∈ J, ∀ M ∈ J, Nonempty (Quot N ≃* Quot M) → N = M := by
  refine exists_continuum_transversal Quot (fun N ↦ ?_) hΓ
  have hsymm : {M : NormalSubgroups Γ | Nonempty (Quot N ≃* Quot M)} =
      {M : NormalSubgroups Γ | Nonempty (Quot M ≃* Quot N)} := by
    ext M
    exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
  rw [hsymm]
  exact countable_iso_class (Quot N)

/-- The family produced above is exactly what
`ContinuumMultiplicity.exists_continuum_pairwise_nonisomorphic` consumes: index by
the
transversal `J`, take `fun i : J ↦ Quot ↑i`, and its two hypotheses are
`hJiso` and `hJcard`.  That composition is left to the caller so that this
file states only the reduction. -/
theorem continuumFamily_hypothesis_of_normalSubgroups
    (Γ : Type) [Group Γ] [Group.FG Γ]
    (hΓ : Cardinal.mk (NormalSubgroups Γ) = Cardinal.continuum) :
    ∃ J : Set (NormalSubgroups Γ), Cardinal.mk J = Cardinal.continuum ∧
      ∀ N ∈ J, ∀ M ∈ J, Nonempty (Quot N ≃* Quot M) → N = M :=
  exists_continuum_pairwise_nonisomorphic_quotients Γ hΓ

end ContinuumFromNormalSubgroups
end GroupApproximation
