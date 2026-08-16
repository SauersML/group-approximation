import GroupApproximation.Monsters.NeumannAlternatingFamily
import GroupApproximation.Sofic.ContinuumMultiplicity
import GroupApproximation.Sofic.ContinuumFamilyCriterion

/-!
# B. H. Neumann's continuum, unconditionally

`non_mf_groups_exist.tex`, the multiplicity paragraph beginning *"Beyond finite
presentation, pairing $E$ with the continuum of pairwise nonisomorphic
two-generator groups of B.~H.~Neumann"* (anchor on the phrase; line numbers
drift).  It concludes that there are `2^{\aleph_0}` pairwise nonisomorphic
finitely generated non-MF groups.  `Sofic/ContinuumMultiplicity` formalizes the
manuscript's own counting step, with Neumann's family entering as a visibly
quantified hypothesis, and `Sofic/ContinuumFamilyCriterion` reduces that
hypothesis to its smallest form: a family of finitely generated groups indexed
by subsets of `ℕ` together with an isomorphism-invariant recovering the subset.
This file supplies both, and so removes the hypothesis.

`Monsters/NeumannAlternatingFamily` constructs, for each set `S ⊆ ℕ`, the
finitely generated group

  `NeumannGroup S = A₅ ≀_{F₂ / markedSubgroup S} F₂`,

shows that the subgroups `markedSubgroup S` are pairwise distinct, and shows
that for a fixed countable `Q` only countably many subgroups `H` give
`A₅ ≀_{F₂/H} F₂ ≅ Q`.  Here that is turned into a continuum of pairwise
nonisomorphic finitely generated groups, by the same countable-fibres argument
that the manuscript uses one level up: a set of size `2^{\aleph_0}` mapping with
countable fibres to isomorphism types has `2^{\aleph_0}` types in its image, and
a transversal of the isomorphism classes is the required family.

There are two endpoints.  `manuscriptContinuumMultiplicityUnconditional` is
`ContinuumMultiplicity.manuscriptContinuumMultiplicity` applied to that family:
a continuum of pairwise nonisomorphic finitely generated groups, each of which
is not operator-MF.  `manuscriptContinuumMultiplicityFromCriterion` discharges
the criterion instead: the transversal is transported along a bijection with the
powerset of `ℕ` (`indexEquiv`), which reindexes the family by subsets of `ℕ`;
since distinct subsets then give nonisomorphic groups, the separating invariant
the criterion asks for is the identity.  The criterion's own economy -- an
invariant in place of a pairwise condition -- is therefore not exploited here:
this construction separates by counting, not by reading off a section set.

The construction is not Neumann's (it is a lamplighter over the coset spaces of
the free group, not a subdirect product of alternating groups) and it produces
finitely generated rather than two-generator groups.  Two-generation is not used
anywhere in the manuscript's deduction, and `Group.FG` is exactly what the Lean
statement consumes.
-/

namespace GroupApproximation

namespace NeumannContinuum

open NeumannFamily ChosenMarkedPresentation

/-! ## Countable fibres for the `ℕ`-indexed family -/

/-- Each member of the family is countable, being finitely generated. -/
theorem countable_neumannGroup (S : Set ℕ) : Countable (NeumannGroup S) :=
  ContinuumMultiplicity.countable_of_fg (NeumannGroup S)

/-- **Countable fibres.**  Only countably many sets of naturals give a member
isomorphic to a fixed member. -/
theorem countable_isomorphic_sets (S : Set ℕ) :
    {T : Set ℕ | Nonempty (NeumannGroup T ≃* NeumannGroup S)}.Countable := by
  haveI : Countable (NeumannGroup S) := countable_neumannGroup S
  have hpre : {T : Set ℕ | Nonempty (NeumannGroup T ≃* NeumannGroup S)}
      = markedSubgroup ⁻¹' {H : Subgroup Acting |
          Nonempty (Wreath AltLamp Acting (Acting ⧸ H) ≃* NeumannGroup S)} :=
    Set.ext fun _ => Iff.rfl
  rw [hpre]
  exact (countable_isomorphic_subgroups (NeumannGroup S)).preimage markedSubgroup_injective

/-! ## A continuum of pairwise nonisomorphic finitely generated groups -/

/-- **Neumann's theorem, in the strength the manuscript uses.**  There is a
continuum-sized set of subsets of `ℕ` whose members give pairwise nonisomorphic
finitely generated groups.

The proof is the counting argument: the isomorphism relation on `Set ℕ` induced
by the family has countable classes, and a set of size `2^{\aleph_0}` covered by
countable classes has `2^{\aleph_0}` classes; a transversal of the classes is
the required index set. -/
theorem exists_continuum_transversal :
    ∃ J : Set (Set ℕ), Cardinal.mk J = Cardinal.continuum ∧
      ∀ S ∈ J, ∀ T ∈ J, Nonempty (NeumannGroup S ≃* NeumannGroup T) → S = T := by
  classical
  -- being isomorphic is an equivalence relation on the index set
  let s : Setoid (Set ℕ) :=
    { r := fun S T => Nonempty (NeumannGroup S ≃* NeumannGroup T)
      iseqv :=
        { refl := fun _ => ⟨MulEquiv.refl _⟩
          symm := fun ⟨e⟩ => ⟨e.symm⟩
          trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ } }
  -- every class is countable
  have hclass : ∀ q : Quotient s, {S : Set ℕ | Quotient.mk s S = q}.Countable := by
    intro q
    have hEq : {S : Set ℕ | Quotient.mk s S = q}
        = {S : Set ℕ | Nonempty (NeumannGroup S ≃* NeumannGroup q.out)} := by
      ext S
      constructor
      · intro hS
        exact Quotient.exact (hS.trans (Quotient.out_eq q).symm)
      · intro hS
        exact (Quotient.sound hS).trans (Quotient.out_eq q)
    rw [hEq]
    exact countable_isomorphic_sets q.out
  haveI hcq : ∀ q : Quotient s, Countable {S : Set ℕ | Quotient.mk s S = q} :=
    fun q => (hclass q).to_subtype
  have huniv : (Set.univ : Set (Set ℕ))
      = ⋃ q : Quotient s, {S : Set ℕ | Quotient.mk s S = q} := by
    ext S
    simp
  have hmkset : Cardinal.mk (Set ℕ) = Cardinal.continuum :=
    ContinuumFamilyCriterion.mk_set_nat
  -- countable classes bound the index set
  have hle : Cardinal.mk (Set ℕ) ≤ Cardinal.mk (Quotient s) * Cardinal.aleph0 := by
    have h1 : Cardinal.mk (Set ℕ)
        = Cardinal.mk (⋃ q : Quotient s, {S : Set ℕ | Quotient.mk s S = q}) := by
      rw [← huniv, Cardinal.mk_univ]
    rw [h1]
    refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
    refine (Cardinal.sum_le_sum _ (fun _ => Cardinal.aleph0) fun q => ?_).trans ?_
    · exact Cardinal.mk_le_aleph0_iff.mpr (hcq q)
    · rw [Cardinal.sum_const']
  have hQle : Cardinal.mk (Quotient s) ≤ Cardinal.continuum := by
    rw [← hmkset]
    exact Cardinal.mk_le_of_surjective Quotient.mk_surjective
  have hQinf : Cardinal.aleph0 < Cardinal.mk (Quotient s) := by
    by_contra hcon
    have hcon' : Cardinal.mk (Quotient s) ≤ Cardinal.aleph0 := not_lt.mp hcon
    have hsmall : Cardinal.mk (Set ℕ) ≤ Cardinal.aleph0 := by
      refine hle.trans ?_
      calc Cardinal.mk (Quotient s) * Cardinal.aleph0
          ≤ Cardinal.aleph0 * Cardinal.aleph0 := by gcongr
        _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0
    rw [hmkset] at hsmall
    exact absurd (hsmall.trans_lt Cardinal.aleph0_lt_continuum) (lt_irrefl _)
  have hQeq : Cardinal.mk (Quotient s) = Cardinal.continuum := by
    refine le_antisymm hQle ?_
    have hmax : Cardinal.mk (Quotient s) * Cardinal.aleph0 = Cardinal.mk (Quotient s) := by
      rw [Cardinal.mul_eq_max hQinf.le le_rfl, max_eq_left hQinf.le]
    rw [← hmkset]
    exact hle.trans hmax.le
  -- a transversal of the classes is the family we want
  refine ⟨Set.range (Quotient.out : Quotient s → Set ℕ), ?_, ?_⟩
  · rw [Cardinal.mk_range_eq _ Quotient.out_injective]
    exact hQeq
  · rintro S ⟨q, rfl⟩ T ⟨p, rfl⟩ he
    have hq : Quotient.mk s q.out = Quotient.mk s p.out := Quotient.sound he
    rw [Quotient.out_eq, Quotient.out_eq] at hq
    rw [hq]

/-! ## The family, packaged for the manuscript's counting step -/

/-- A continuum-sized transversal of the isomorphism classes. -/
noncomputable def transversal : Set (Set ℕ) := exists_continuum_transversal.choose

theorem mk_transversal : Cardinal.mk transversal = Cardinal.continuum :=
  exists_continuum_transversal.choose_spec.1

theorem transversal_pairwise :
    ∀ S ∈ transversal, ∀ T ∈ transversal,
      Nonempty (NeumannGroup S ≃* NeumannGroup T) → S = T :=
  exists_continuum_transversal.choose_spec.2

/-- The index type of the family: a continuum of subsets of `ℕ`. -/
noncomputable abbrev NeumannIndex : Type := ↥transversal

/-- The family itself: a continuum of pairwise nonisomorphic finitely generated
groups. -/
noncomputable abbrev NeumannFamilyGroup (i : NeumannIndex) : Type :=
  NeumannGroup (i : Set ℕ)

/-- The index type has the cardinality of the continuum. -/
theorem mk_neumannIndex : Cardinal.mk NeumannIndex = Cardinal.continuum := mk_transversal

/-- **The family is pairwise nonisomorphic.** -/
theorem neumannFamily_pairwise (i j : NeumannIndex) :
    Nonempty (NeumannFamilyGroup i ≃* NeumannFamilyGroup j) → i = j := fun h =>
  Subtype.ext (transversal_pairwise (i : Set ℕ) i.2 (j : Set ℕ) j.2 h)

/-- **B. H. Neumann's statement, as the manuscript uses it, with no hypothesis
left.**  There is a continuum of pairwise nonisomorphic finitely generated
groups. -/
theorem neumann_continuum_of_finitely_generated_groups :
    Cardinal.mk NeumannIndex = Cardinal.continuum ∧
      (∀ i : NeumannIndex, Group.FG (NeumannFamilyGroup i)) ∧
      ∀ i j : NeumannIndex, Nonempty (NeumannFamilyGroup i ≃* NeumannFamilyGroup j) → i = j :=
  ⟨mk_neumannIndex, fun i => instFGNeumannGroup (i : Set ℕ), neumannFamily_pairwise⟩

/-! ## Re-indexing by subsets of `ℕ`: the criterion's exact shape -/

/-- The transversal and the powerset of `ℕ` are both continuum-sized, hence in
bijection. -/
theorem nonempty_equiv_transversal : Nonempty (Set ℕ ≃ NeumannIndex) :=
  Cardinal.eq.mp (ContinuumFamilyCriterion.mk_set_nat.trans mk_transversal.symm)

/-- A bijection from the powerset of `ℕ` onto the transversal. -/
noncomputable def indexEquiv : Set ℕ ≃ NeumannIndex :=
  Classical.choice nonempty_equiv_transversal

/-- **The family indexed by subsets of `ℕ`.**  The transversal transported along
`indexEquiv`: one finitely generated group for every subset of `ℕ`, with distinct
subsets giving nonisomorphic groups. -/
noncomputable abbrev SubsetFamily (S : Set ℕ) : Type :=
  NeumannGroup ((indexEquiv S : NeumannIndex) : Set ℕ)

instance instFGSubsetFamily (S : Set ℕ) : Group.FG (SubsetFamily S) :=
  instFGNeumannGroup _

/-- **The separating invariant is the identity.**  Distinct subsets give
nonisomorphic members, so `id : Set ℕ → Set ℕ` is an isomorphism-invariant
recovering the subset -- exactly the datum `ContinuumFamilyCriterion` asks for. -/
theorem subsetFamily_separating (S T : Set ℕ) :
    Nonempty (SubsetFamily S ≃* SubsetFamily T) → S = T := by
  intro h
  have hval : ((indexEquiv S : NeumannIndex) : Set ℕ)
      = ((indexEquiv T : NeumannIndex) : Set ℕ) :=
    transversal_pairwise _ (indexEquiv S).2 _ (indexEquiv T).2 h
  exact indexEquiv.injective (Subtype.ext hval)

/-- **The remaining obligation of `Sofic/ContinuumFamilyCriterion`, discharged.**
A family of finitely generated groups indexed by subsets of `ℕ`, together with an
isomorphism-invariant recovering the subset, fed to
`manuscriptContinuumMultiplicity_of_subsetSeparating`. -/
theorem manuscriptContinuumMultiplicityFromCriterion :
    ∃ J : Set (Set ℕ), Cardinal.mk J = Cardinal.continuum ∧
      (∀ S ∈ J, Group.FG (MarkedGroup × SubsetFamily S) ∧
        ¬ IsOperatorMF (MarkedGroup × SubsetFamily S)) ∧
      ∀ S ∈ J, ∀ T ∈ J,
        Nonempty ((MarkedGroup × SubsetFamily S) ≃*
          (MarkedGroup × SubsetFamily T)) → S = T :=
  ContinuumFamilyCriterion.manuscriptContinuumMultiplicity_of_subsetSeparating
    SubsetFamily (id : Set ℕ → Set ℕ) subsetFamily_separating Function.injective_id

/-! ## The manuscript's continuum multiplicity, with the hypothesis discharged -/

/-- **Continuum multiplicity, unconditionally.**  The manuscript's counting step
`ContinuumMultiplicity.manuscriptContinuumMultiplicity` applied to the family
built here: there is a continuum of pairwise nonisomorphic finitely generated
groups, each of them not operator-MF.

This is the statement the manuscript makes at lines 3300-3320 of
`non_mf_groups_exist.tex`, with its one literature input -- the existence of
Neumann's continuum family -- now proved rather than assumed. -/
theorem manuscriptContinuumMultiplicityUnconditional :
    ∃ J : Set NeumannIndex, Cardinal.mk J = Cardinal.continuum ∧
      (∀ i ∈ J, Group.FG (MarkedGroup × NeumannFamilyGroup i) ∧
        ¬ IsOperatorMF (MarkedGroup × NeumannFamilyGroup i)) ∧
      ∀ i ∈ J, ∀ j ∈ J,
        Nonempty ((MarkedGroup × NeumannFamilyGroup i) ≃*
          (MarkedGroup × NeumannFamilyGroup j)) → i = j :=
  ContinuumMultiplicity.manuscriptContinuumMultiplicity NeumannFamilyGroup
    neumannFamily_pairwise mk_neumannIndex

end NeumannContinuum

end GroupApproximation
