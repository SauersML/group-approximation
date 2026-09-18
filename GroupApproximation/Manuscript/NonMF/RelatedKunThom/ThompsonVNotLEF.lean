import GroupApproximation.Leavitt.ThompsonVWitness
import GroupApproximation.Manuscript.SimpleKazhdanSofic.QuestionsNotFinitelyPresented
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Kun--Thom paragraph): a copy of Thompson's group `V` is not LEF

The census row `de554b7cd342` covers the related-work sentence of
`non_mf_groups_exist.tex`, lines 339--342:

> There, soficity and the rigidity theorems of Kun~\cite{Kun16} and
> Kun--Thom~\cite{KT19} force the centralizing subgroup to be locally embeddable
> into finite groups, and a copy of Thompson's group `V` gives the contradiction.

This module proves the contradiction step, (2) of the sentence: no group
containing a copy of `V` is LEF. The rigidity step (1) and the closed endpoint
are in `RelatedKunThom/Endpoint.lean`.

## Proof route

* The classical principle: a finitely presented LEF group is residually finite
  (`SimpleKazhdanSofic.printedFinitelyPresentedLEFResiduallyFinite`), and an
  infinite simple group is not residually finite
  (`NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite`).
  So a finitely presented infinite simple group is not LEF
  (`not_isLEF_of_finitelyPresented_simple_infinite`).
* The corpus model of `V` is `ThompsonV.thompsonV`, a subgroup of the
  permutations of Cantor space `ℕ → Fin 2`. It is not LEF
  (`BinaryLeavitt.thompsonV_not_isLEF`): the non-LEF corner witness subgroup
  of the Leavitt family over `ZMod 2` embeds into it through the stream action.
  The corpus does not formalize the finite presentation or simplicity of `V`,
  so this route replaces the classical one for `V` itself. The printed sentence
  only uses the fact that `V` is not LEF.
* LEF passes to subgroups (`isLEF_of_injective`), so any group containing an
  injective copy of `V` is not LEF (`not_isLEF_of_thompsonV_embedding`).
  Finite groups are LEF (`isLEF_of_finite`), so `V` is infinite
  (`thompsonV_infinite`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedKunThom

/-- **Finitely presented + infinite simple ⇒ not LEF.** A finitely presented LEF
group is residually finite, and an infinite simple group is not residually
finite. -/
theorem not_isLEF_of_finitelyPresented_simple_infinite
    (E : Type) [Group E] [IsSimpleGroup E] [Infinite E]
    (hfp : Group.IsFinitelyPresented E) : ¬ IsLEF E := fun hLEF =>
  GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite E
    (GroupApproximation.SimpleKazhdanSofic.printedFinitelyPresentedLEFResiduallyFinite.{0}
      E hfp hLEF)

/-- Thompson's group `V` (the corpus model) is infinite: finite groups are LEF,
and `V` is not. -/
theorem thompsonV_infinite : Infinite ↥GroupApproximation.ThompsonV.thompsonV := by
  refine not_finite_iff_infinite.mp ?_
  intro h
  exact GroupApproximation.BinaryLeavitt.thompsonV_not_isLEF
    (@GroupApproximation.isLEF_of_finite _ _ h)

/-- **A copy of `V` obstructs LEF.** A group that contains an injective
homomorphic image of Thompson's group `V` is not LEF. -/
theorem not_isLEF_of_thompsonV_embedding {E : Type*} [Group E]
    (ι : ↥GroupApproximation.ThompsonV.thompsonV →* E) (hι : Function.Injective ι) :
    ¬ IsLEF E := fun hE =>
  GroupApproximation.BinaryLeavitt.thompsonV_not_isLEF
    (GroupApproximation.isLEF_of_injective ι hι hE)

end RelatedKunThom
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedKunThom.not_isLEF_of_finitelyPresented_simple_infinite
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedKunThom.thompsonV_infinite
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedKunThom.not_isLEF_of_thompsonV_embedding
