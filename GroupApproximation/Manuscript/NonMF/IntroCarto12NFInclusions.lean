import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Manuscript.NonMF.RelatedAttribution.MFNotionsAndQuestions
import GroupApproximation.Manuscript.NonMF.RelatedTWW.Definitions
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): the NF inclusions

Census row `5d8b94bc850e`, `non_mf_groups_exist.tex` L310--312 (Related work):

> They wrote that the classes of NF, strong NF, and separable nuclear stably
> finite $C^*$-algebras might coincide.

"Might coincide" is a conjecture attributed to Blackadar and Kirchberg, not a
claim of the manuscript. The mathematical content behind it is that the three
classes are nested: strong NF ⊆ NF ⊆ separable nuclear stably finite. This module
proves the second inclusion and records quasidiagonality on the way, since NF
algebras are exactly the nuclear quasidiagonal ones.

## What is proved

* `manuscriptSentence_nfSubsetSeparableNuclearStablyFinite` is **unconditional**.
  An NF algebra (`IsNFAlgebra`, the finite-local CPC predicate of
  `Analysis/NFAlgebra.lean`) is separable, nuclear and stably finite. The route:
  `IsNFAlgebra.separable_nuclear_and_mf` gives separable, nuclear and MF (this is
  the same forward half as `RelatedBK.manuscriptSentence_blackadarKirchbergNFForward`),
  and `RelatedAttribution.isStablyFiniteCStarAlgebra_of_isMFAlgebra` turns MF into
  stable finiteness (an isometry in a matrix amplification of an MF algebra is a
  unitary).
* `manuscriptSentence_nfSubsetNuclearStablyFiniteQD_of_nfImpliesQuasidiagonal`
  gives the lane target (the four-fold conjunction including
  `IsQuasidiagonalCStarAlgebra`) from `NFImpliesQuasidiagonalStatement`.

## The remaining interface

`NFImpliesQuasidiagonalStatement` says that every NF algebra is quasidiagonal.
It is the target of lane nm-intro-09 (`isQuasidiagonalCStarAlgebra_of_isNFAlgebra`),
which is not yet on disk. The statement is **true**. A dense sequence `(aₖ)`,
the finite sets `Fₙ = {a₀, …, aₙ}` and tolerances `1/(n+1)` give local NF
approximations `downₙ : A → M_{Dₙ}`. These are contractive, star-preserving (as
completely positive maps) and asymptotically multiplicative on the dense sequence,
hence on all of `A` by a 3ε argument. Norm recovery follows from
`‖a‖ ≤ ‖upₙ(downₙ a)‖ + ε ≤ ‖downₙ a‖ + ε`. The zero algebra is handled separately.

It is strictly smaller in proof content than the lane target: the target is its
conclusion conjoined with the three unconditional clauses proved here. It is not
a restatement of the target, and it bundles no literature input.

Strong NF is not defined here. A faithful definition needs generalized inductive
limits with complete order embeddings, and the lane forbids an unfaithful proxy.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto12

open CStarExactness
open GroupApproximation.Manuscript.NonMF.RelatedTWW

universe u

/-- **NF ⇒ quasidiagonal** (Blackadar--Kirchberg), the interface of lane
nm-intro-09. Every C⋆-algebra satisfying the finite-local NF predicate is
quasidiagonal, in the sense of `RelatedTWW.IsQuasidiagonalCStarAlgebra`
(separable, with a quasidiagonal matrix model). -/
def NFImpliesQuasidiagonalStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A → IsQuasidiagonalCStarAlgebra A

/-- **tex 310--312, the inclusion NF ⊆ separable nuclear stably finite.** Every NF
C⋆-algebra is separable, nuclear and stably finite. No hypothesis beyond NF is
used. -/
theorem manuscriptSentence_nfSubsetSeparableNuclearStablyFinite
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) :
    TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A ∧
      IsStablyFiniteCStarAlgebra A :=
  ⟨hA.separable, hA.isNuclearCStarAlgebra,
    RelatedAttribution.isStablyFiniteCStarAlgebra_of_isMFAlgebra hA.isMFAlgebra⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto12.manuscriptSentence_nfSubsetSeparableNuclearStablyFinite

/-- **tex 310--312, the NF inclusions with quasidiagonality**, modulo the
lane nm-intro-09 interface. Every NF C⋆-algebra is separable, nuclear, stably
finite and quasidiagonal. -/
theorem manuscriptSentence_nfSubsetNuclearStablyFiniteQD_of_nfImpliesQuasidiagonal
    (hQD : NFImpliesQuasidiagonalStatement.{u})
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) :
    TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A ∧
      IsStablyFiniteCStarAlgebra A ∧ IsQuasidiagonalCStarAlgebra A :=
  ⟨hA.separable, hA.isNuclearCStarAlgebra,
    RelatedAttribution.isStablyFiniteCStarAlgebra_of_isMFAlgebra hA.isMFAlgebra,
    hQD A hA⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto12.manuscriptSentence_nfSubsetNuclearStablyFiniteQD_of_nfImpliesQuasidiagonal

/-- The class inclusion as a proposition over all C⋆-algebras in a universe:
the NF class lies inside the class of separable nuclear stably finite algebras.
This is the direction of the conjectured coincidence that holds. -/
theorem manuscriptSentence_nfClassSubsetSeparableNuclearStablyFiniteClass :
    ∀ (A : Type u) [CStarAlgebra A], IsNFAlgebra A →
      TopologicalSpace.SeparableSpace A ∧ IsNuclearCStarAlgebra A ∧
        IsStablyFiniteCStarAlgebra A :=
  fun _ _ hA => manuscriptSentence_nfSubsetSeparableNuclearStablyFinite hA

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto12.manuscriptSentence_nfClassSubsetSeparableNuclearStablyFiniteClass

end IntroCarto12
end NonMF
end Manuscript
end GroupApproximation
