import GroupApproximation.Manuscript.NonMF.RelatedKunThom.ThompsonVNotLEF
import GroupApproximation.Criterion.CriterionAssembly
import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work: Kun--Thom rigidity and the Thompson `V` contradiction

The census row `de554b7cd342` covers the related-work sentence of
`non_mf_groups_exist.tex`, lines 339--342. It follows lines 336--339:

> Theorem~\ref{thm:compression-criterion} uses the configuration of the nonsofic
> construction~\cite[Proposition~2.3]{OAI}: a property-(T) subgroup `L`
> conjugated into itself by an element `u`, and an element `c` commuting with `L`
> whose conjugate `u c u⁻¹` does not.
> There, soficity and the rigidity theorems of Kun~\cite{Kun16} and
> Kun--Thom~\cite{KT19} force the centralizing subgroup to be locally embeddable
> into finite groups, and a copy of Thompson's group `V` gives the contradiction.

Bibliography (tex lines 2422, 2428, 2459):
* `Kun16`: G. Kun, *On sofic approximations of property (T) groups*,
  arXiv:1606.04471.
* `KT19`: G. Kun and A. Thom, *Inapproximability of actions and Kazhdan's
  property (T)*, arXiv:1901.03963.
* `OAI`: *Nonsofic groups exist*, Proposition 2.3.

## Where "there" lives in the corpus

The configuration of [OAI, Prop. 2.3] is `CompressionSetup G Γ J`:
* a finitely generated infinite property-(T) group `Γ` embedded in `G`;
* the centralizing subgroup `J` embedded in `Γ`;
* compressors, including a distinguished `u` with `u Γ u⁻¹` commuting with `J`
  and meeting it trivially.

## Proof route (reused, not reproved)

1. **Kun's rigidity theorem.** `KunFixedDecomposition.expanderDecomposition`:
   every sofic approximation of an infinite property-(T) group has an expander
   decomposition on any finite symmetric generating set containing `1`. This
   is proved in `GroupApproximation/Kun/*`.
2. **Kun--Thom rigidity and the LEF conclusion.**
   `CriterionAssembly.isLEF_of_soficApproximation` and `isLEF_of_isSofic` prove
   that a sofic ambient group of a compression setup with `(T)` forces `J` to be
   LEF. The route: Kun decompositions for `G` and `Γ`, then the conservative
   matching, then the Kun--Thom matching certificate
   (`KunThomEssential.isLEF_of_matchingCertificate`, via `SelectionOutput.isLEF`).
3. **The contradiction.** See `RelatedKunThom/ThompsonVNotLEF.lean`:
   * finitely presented + infinite simple ⇒ not LEF;
   * `V` is infinite and not LEF;
   * a group containing a copy of `V` is not LEF.
   So a compression setup with `(T)` whose `J` contains a copy of `V` has a
   nonsofic ambient group.
4. **The configuration is realized.** The universal rank-four Leavitt setup has
   `(T)` on `G` and `Γ`, a non-LEF centralizing subgroup (the corner witness,
   which embeds into `V`, rather than the other way round), and a nonsofic
   ambient group. We make no claim that `V` embeds into this `J`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedKunThom

/-- **Tex lines 339--342.** Closed form of the related-work sentence.

1. *Kun's theorem.* Sofic approximations of infinite property-(T) groups admit
   expander decompositions on finite symmetric generating sets.
2. *Rigidity step.* In the compression configuration with `(T)` on `G` and `Γ`,
   a sofic approximation of `G` (in particular soficity of a countable `G`)
   forces the centralizing subgroup `J` to be LEF.
3. *Classical principle.* A finitely presented LEF group is residually finite,
   an infinite simple group is not, so a finitely presented infinite simple group
   is not LEF.
4. *Thompson's `V`.* `V` is infinite and not LEF, and no group containing a copy
   of `V` is LEF.
5. *The contradiction.* A compression setup with `(T)` whose centralizing
   subgroup contains a copy of `V` has a nonsofic ambient group.
6. *Realization.* The universal rank-four Leavitt compression setup has `(T)`,
   a non-LEF centralizing subgroup, and a nonsofic ambient group. -/
theorem manuscriptSentence_kunThomRigidityThompsonVContradiction :
    (∀ (G : Type) [Group G] [Infinite G], HasKazhdanPropertyT.{0, 0} G →
      ∀ S : Finset G, 1 ∈ S → (∀ g ∈ S, g⁻¹ ∈ S) →
        Subgroup.closure (S : Set G) = ⊤ →
        ∀ A : SoficApproximation G, Nonempty (ExpanderDecomposition A S)) ∧
    (∀ (G Γ J : Type) [Group G] [Group Γ] [Group J] [Countable Γ] [Countable J],
      CompressionSetup G Γ J → HasKazhdanPropertyT.{0, 0} G →
        HasKazhdanPropertyT.{0, 0} Γ → SoficApproximation G → IsLEF J) ∧
    (∀ (G Γ J : Type) [Group G] [Group Γ] [Group J]
        [Countable G] [Countable Γ] [Countable J],
      CompressionSetup G Γ J → HasKazhdanPropertyT.{0, 0} G →
        HasKazhdanPropertyT.{0, 0} Γ → IsSofic G → IsLEF J) ∧
    (∀ (E : Type) [Group E], Group.IsFinitelyPresented E → IsLEF E →
      IsResiduallyFinite E) ∧
    (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E], ¬ IsResiduallyFinite E) ∧
    (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E],
      Group.IsFinitelyPresented E → ¬ IsLEF E) ∧
    (Infinite ↥ThompsonV.thompsonV ∧ ¬ IsLEF ↥ThompsonV.thompsonV) ∧
    (∀ (E : Type) [Group E],
      (∃ ι : ↥ThompsonV.thompsonV →* E, Function.Injective ι) → ¬ IsLEF E) ∧
    (∀ (G Γ J : Type) [Group G] [Group Γ] [Group J]
        [Countable G] [Countable Γ] [Countable J],
      CompressionSetup G Γ J → HasKazhdanPropertyT.{0, 0} G →
        HasKazhdanPropertyT.{0, 0} Γ →
        (∃ ι : ↥ThompsonV.thompsonV →* J, Function.Injective ι) → ¬ IsSofic G) ∧
    (Nonempty (CompressionSetup UniversalRankFour.Ambient UniversalRankFour.Core
        UniversalRankFour.Witness) ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Core ∧
      ¬ IsLEF UniversalRankFour.Witness ∧
      ¬ IsSofic UniversalRankFour.Ambient) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G _ _ hT S hone hsymm hgen A
    exact GroupApproximation.KunFixedDecomposition.expanderDecomposition
      hT S hone hsymm hgen A
  · intro G Γ J _ _ _ _ _ C hTG hTΓ A
    exact GroupApproximation.isLEF_of_soficApproximation C hTG hTΓ A
  · intro G Γ J _ _ _ _ _ _ C hTG hTΓ hS
    exact GroupApproximation.isLEF_of_isSofic C hTG hTΓ hS
  · intro E _ hfp hLEF
    exact GroupApproximation.SimpleKazhdanSofic.printedFinitelyPresentedLEFResiduallyFinite.{0}
      E hfp hLEF
  · intro E _ _ _
    exact GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite
      E
  · intro E _ _ _ hfp
    exact not_isLEF_of_finitelyPresented_simple_infinite E hfp
  · exact ⟨thompsonV_infinite, GroupApproximation.BinaryLeavitt.thompsonV_not_isLEF⟩
  · rintro E _ ⟨ι, hι⟩
    exact not_isLEF_of_thompsonV_embedding ι hι
  · rintro G Γ J _ _ _ _ _ _ C hTG hTΓ ⟨ι, hι⟩ hS
    exact not_isLEF_of_thompsonV_embedding ι hι
      (GroupApproximation.isLEF_of_isSofic C hTG hTΓ hS)
  · exact ⟨⟨GroupApproximation.UniversalRankFour.compressionSetup⟩,
      GroupApproximation.UniversalRankFour.ambient_hasKazhdanPropertyT.{0},
      GroupApproximation.UniversalRankFour.core_hasKazhdanPropertyT.{0},
      GroupApproximation.UniversalRankFour.witness_not_isLEF,
      GroupApproximation.universalLeavittEL4_not_isSofic⟩

end RelatedKunThom
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.RelatedKunThom.manuscriptSentence_kunThomRigidityThompsonVContradiction
