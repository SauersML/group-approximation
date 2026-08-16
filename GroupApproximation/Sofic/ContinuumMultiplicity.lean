import GroupApproximation.Sofic.ContinuumMultiplicityCore
import GroupApproximation.Monsters.NeumannContinuum

/-!
# Continuum multiplicity of the non-MF phenomenon

The manuscript's continuum paragraph prints three things, and the badge on this
module has to carry all three.

1. **The deduction.**  "Pairing `E` with a continuum of pairwise nonisomorphic
   finitely generated groups yields `2^{ℵ₀}` pairwise nonisomorphic finitely
   generated non-MF groups", by the counting argument — a fixed countable group
   is isomorphic to `E × N` for only countably many types `N`, and a map with
   countable fibres from a continuum-sized family has continuum-sized image.
   The manuscript is explicit that this half is general: "the deduction uses
   only that the `N` are finitely generated".
2. **The construction.**  "Such a continuum is constructed in the accompanying
   development, as a lamplighter over coset spaces of the free group rather
   than as a subdirect product of alternating groups."
3. **The conclusion**, which is (1) applied to (2) and carries no hypothesis:
   there are `2^{ℵ₀}` pairwise nonisomorphic finitely generated non-MF groups.

Until now the badged declaration stated only (1), with the family entering as
the quantified premises `(N : ι → Type)`, pairwise nonisomorphism and
`Cardinal.mk ι = Cardinal.continuum`.  That is what
`scripts/check_non_mf_unconditional.py` reported: a reader of the badge alone
could not tell whether the corpus builds such a family or quotes B. H. Neumann
for it.  It builds one — `Monsters/NeumannAlternatingFamily` constructs
`A₅ ≀_{F₂/markedSubgroup S} F₂` for every `S ⊆ ℕ`, and `Monsters/NeumannContinuum`
extracts a continuum-sized pairwise nonisomorphic transversal by the same
countable-fibres argument used one level up — so the repair is to say so in the
badged statement.

`manuscriptContinuumMultiplicity` below therefore has three conjuncts, one per
printed sentence, with all quantifiers inside the proposition and no premises.
Neumann's sharper two-generator form is not needed and is not used; the
construction produces finitely generated groups, which is all the counting step
consumes.

The counting step itself now lives one module up, in
`Sofic/ContinuumMultiplicityCore`, under the same namespace, because the
construction consumes it and this file consumes the construction.  Callers of
`countable_of_fg`, `countable_fg_subgroups`, `fg_prod`,
`countable_isomorphic_indices` and `exists_continuum_pairwise_nonisomorphic`
are unaffected: the names did not change, only the file they are declared in.
-/

namespace GroupApproximation
namespace ContinuumMultiplicity

open ProductMultiplicity ChosenMarkedPresentation

/-- **The manuscript's continuum-multiplicity paragraph, in the form it is
printed.**

The conjuncts follow the printed sentences:

* the deduction, for an arbitrary continuum-sized family of pairwise
  nonisomorphic finitely generated groups — this is the half the manuscript
  says "uses only that the `N` are finitely generated";
* such a family exists: a continuum of pairwise nonisomorphic finitely
  generated groups is *constructed*, not assumed, which is the direct answer to
  "the corpus never exhibits one";
* hence, with nothing assumed, a continuum of pairwise nonisomorphic finitely
  generated groups none of which is operator-MF.

The third conjunct is the printed headline and is what the second makes
unconditional.  Note that the third is genuinely stronger than the first
applied blindly: the products `E × N` need not be pairwise nonisomorphic even
when the `N` are, so the family it exhibits is a transversal of the
isomorphism classes of the products, which is what the counting step
produces. -/
theorem manuscriptContinuumMultiplicity :
    (∀ {ι : Type} (N : ι → Type) [∀ i, Group (N i)] [∀ i, Group.FG (N i)],
      (∀ i j : ι, Nonempty (N i ≃* N j) → i = j) →
        Cardinal.mk ι = Cardinal.continuum →
        ∃ J : Set ι, Cardinal.mk J = Cardinal.continuum ∧
          (∀ i ∈ J, Group.FG (MarkedGroup × N i) ∧
            ¬ IsOperatorMF (MarkedGroup × N i)) ∧
          ∀ i ∈ J, ∀ j ∈ J,
            Nonempty ((MarkedGroup × N i) ≃* (MarkedGroup × N j)) → i = j) ∧
    (∃ (ι : Type) (N : ι → Type) (_ : ∀ i, Group (N i)),
      Cardinal.mk ι = Cardinal.continuum ∧
        (∀ i, Group.FG (N i)) ∧
        ∀ i j : ι, Nonempty (N i ≃* N j) → i = j) ∧
    (∃ (ι : Type) (P : ι → Type) (_ : ∀ i, Group (P i)),
      Cardinal.mk ι = Cardinal.continuum ∧
        (∀ i, Group.FG (P i) ∧ ¬ IsOperatorMF (P i)) ∧
        ∀ i j : ι, Nonempty (P i ≃* P j) → i = j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ι N _ _ hfam hcard
    exact exists_continuum_pairwise_nonisomorphic N hfam hcard
  · obtain ⟨hcard, hfg, hpair⟩ :=
      NeumannContinuum.neumann_continuum_of_finitely_generated_groups
    exact ⟨NeumannContinuum.NeumannIndex, NeumannContinuum.NeumannFamilyGroup,
      fun _ ↦ inferInstance, hcard, hfg, hpair⟩
  · obtain ⟨J, hJcard, hJmem, hJpair⟩ :=
      NeumannContinuum.manuscriptContinuumMultiplicityUnconditional
    refine ⟨↥J,
      fun i ↦ MarkedGroup × NeumannContinuum.NeumannFamilyGroup
        (i : NeumannContinuum.NeumannIndex),
      fun _ ↦ inferInstance, hJcard, fun i ↦ hJmem (i : _) i.2, ?_⟩
    rintro i j he
    exact Subtype.ext (hJpair (i : _) i.2 (j : _) j.2 he)

end ContinuumMultiplicity
end GroupApproximation
