import GroupApproximation.Sofic.ContinuumMultiplicityCore

/-!
# The remaining obligation behind continuum multiplicity

`Sofic.ContinuumMultiplicityCore` proves the manuscript's counting step on top of
a quantified hypothesis: a continuum-sized family of pairwise nonisomorphic
finitely generated groups.  The manuscript attributed that hypothesis to
B. H. Neumann and quoted it.

**It is no longer quoted.**  `Monsters.NeumannContinuum` imports this file and
discharges the obligation stated below outright, at
`manuscriptContinuumMultiplicityFromCriterion`, with the lamplighters
`A₅ ≀_{F₂/markedSubgroup S} F₂` over subsets `S ⊆ ℕ`; the manuscript's
sentence is then unconditional at
`manuscriptContinuumMultiplicityUnconditional`.  The family is not Neumann's
and is finitely generated rather than two-generator, which is all the counting
step consumes.

What this file contributes is the reduction that made that possible: it makes
the obligation as small and as concrete as it can honestly be made, so that a
construction has nothing to supply but the construction:

* `manuscriptContinuumMultiplicity_of_separating` replaces "pairwise
  nonisomorphic" --- a condition on every pair --- by an *invariant*: any map
  out of the index set that is constant on isomorphism classes and injective.
  This is the shape every known construction actually produces (Neumann's
  invariant is the set of alternating groups occurring as sections), and it is
  strictly easier to supply than the pairwise statement.
* `mk_set_nat` removes the cardinal bookkeeping: a family indexed by subsets
  of `ℕ` is automatically continuum-sized.
* `manuscriptContinuumMultiplicity_of_subsetSeparating` combines the two, so
  the entire remaining obligation is: *a family of finitely generated groups
  indexed by subsets of `ℕ`, together with an isomorphism-invariant that
  recovers the subset.*

Nothing here is deep --- the separating-invariant criterion is a two-line
consequence of the counting step.  It is recorded because the value was in the
statement, not the proof: it named, in one closed proposition, exactly what was
missing, and it certified that supplying it was sufficient.  The analogue for
the one remaining open literature input is
`Computability.MarkovMFConsequences.AdianRabinReduction`, which plays the same
role for Adian--Rabin and has not been discharged.
-/

namespace GroupApproximation
namespace ContinuumFamilyCriterion

open ProductMultiplicity ChosenMarkedPresentation

/-- The powerset of the naturals is continuum-sized, so a family indexed by
subsets of `ℕ` carries no cardinal obligation. -/
theorem mk_set_nat : Cardinal.mk (Set ℕ) = Cardinal.continuum := by
  rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0]

/-- **Continuum multiplicity from a separating invariant.**  Pairwise
nonisomorphism is a condition on every pair; an invariant that is constant on
isomorphism classes and injective supplies it uniformly, and is what an actual
construction produces. -/
theorem manuscriptContinuumMultiplicity_of_separating :
    ∀ {ι : Type} (N : ι → Type) [∀ i, Group (N i)] [∀ i, Group.FG (N i)]
      {β : Type} (inv : ι → β),
      (∀ i j : ι, Nonempty (N i ≃* N j) → inv i = inv j) →
      Function.Injective inv →
      Cardinal.mk ι = Cardinal.continuum →
      ∃ J : Set ι, Cardinal.mk J = Cardinal.continuum ∧
        (∀ i ∈ J, Group.FG (MarkedGroup × N i) ∧
          ¬ IsOperatorMF (MarkedGroup × N i)) ∧
        ∀ i ∈ J, ∀ j ∈ J,
          Nonempty ((MarkedGroup × N i) ≃* (MarkedGroup × N j)) → i = j := by
  intro ι N _ _ β inv hinv hinj hcard
  refine ContinuumMultiplicity.exists_continuum_pairwise_nonisomorphic N ?_ hcard
  intro i j hij
  exact hinj (hinv i j hij)

/-- **The obligation in its smallest form.**  Everything except the
construction is discharged: index by subsets of `ℕ`, supply finite generation,
and supply an isomorphism-invariant that recovers the subset. -/
theorem manuscriptContinuumMultiplicity_of_subsetSeparating :
    ∀ (N : Set ℕ → Type) [∀ S, Group (N S)] [∀ S, Group.FG (N S)]
      {β : Type} (inv : Set ℕ → β),
      (∀ S T : Set ℕ, Nonempty (N S ≃* N T) → inv S = inv T) →
      Function.Injective inv →
      ∃ J : Set (Set ℕ), Cardinal.mk J = Cardinal.continuum ∧
        (∀ S ∈ J, Group.FG (MarkedGroup × N S) ∧
          ¬ IsOperatorMF (MarkedGroup × N S)) ∧
        ∀ S ∈ J, ∀ T ∈ J,
          Nonempty ((MarkedGroup × N S) ≃* (MarkedGroup × N T)) → S = T := by
  intro N _ _ β inv hinv hinj
  exact manuscriptContinuumMultiplicity_of_separating N inv hinv hinj mk_set_nat

end ContinuumFamilyCriterion
end GroupApproximation
