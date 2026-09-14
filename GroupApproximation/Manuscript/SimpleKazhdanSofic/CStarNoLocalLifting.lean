import GroupApproximation.Analysis.LocalLiftingFactorization
import GroupApproximation.Analysis.HyperlinearTraceVanishingProof
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Manuscript.NinetyNineProblems.KirchbergTheorem
import GroupApproximation.Sofic.ContinuumMultiplicityCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The full C⋆-algebra of an infinite simple Kazhdan hyperlinear group has no local lifting property

`simple_kazhdan_sofic_group.tex` at 8b36733d7, Introduction, tex l.51–54
(l.49–52 at f34e9c0b1):

> Ozawa stated the hyperlinear form in 2003, noting that the full
> $C^*$-algebra of such a group cannot have the local lifting
> property~\cite[p.~527]{Ozawa}, and Pestov's Open question~9.1 adds the
> sofic form~\cite{Pestov}.

"Such a group" is an infinite simple group with property (T) that is
hyperlinear.  This module carries the mathematical claim of the sentence.
The attributions are credit.

Ozawa, *About the QWEP conjecture*, Internat. J. Math. **15** (2004), p. 527
(preprint p. 26): "It is unknown whether there exists a simple property (T)
group Γ which is hyperlinear.  By the above theorem, the full C⋆-algebra C⋆Γ of
such a group Γ cannot have the LLP."

Route.
* A Kazhdan group is finitely generated
  (`KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`), hence countable.
* A countable hyperlinear group has a trace-preserving matrix model
  (`HyperlinearTraceVanishing.hyperlinearTracePreservingModelStatement_holds`,
  step one of Ozawa's Proposition 7.1).
* If `C⋆(G)` had the LLP, `G` would have the factorization property
  (`LocalLifting.localLiftingFactorizationStatement_holds`: Ozawa p. 24, local
  ucp lifts and Arveson extension).
* An infinite simple Kazhdan group does not have the factorization property
  (`NinetyNineProblems.not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan`).
  That result is Kirchberg's Theorem 1.1 together with
  `not_isResiduallyFinite_of_isSimpleGroup_of_infinite`.

`printedOzawaNoLocalLiftingGeneral` is closed.  It applies
`printedOzawaNoLocalLiftingGeneral_of_kirchberg` to oa-kirchberg's inhabitant
`NinetyNineProblems.KirchbergTheorem.kirchbergKazhdanFactorizationInput` of
Kirchberg's Theorem 1.1.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open LocalLifting NinetyNineProblems

/-- **No local lifting property without the factorization property.**  For a
countable hyperlinear group, a full C⋆-algebra with the LLP would give the
factorization property. -/
theorem not_hasLocalLiftingProperty_of_not_hasFactorizationProperty
    (G : Type) [Group G] [Countable G] (hH : IsHyperlinear G)
    (hF : ¬ HasFactorizationProperty G) :
    ¬ HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G) := fun hLLP ↦
  hF (localLiftingFactorizationStatement_holds G hLLP
    (HyperlinearTraceVanishing.hyperlinearTracePreservingModelStatement_holds.{0} G hH))

/-- tex l.51–54 at 8b36733d7: the full C⋆-algebra of an infinite simple
hyperlinear group with property (T) cannot have the local lifting property. -/
def PrintedOzawaNoLocalLiftingGeneral : Prop :=
  ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G],
    HasKazhdanPropertyT.{0, 0} G → IsHyperlinear G →
      ¬ HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G)

/-- tex l.51–54 at 8b36733d7, over Kirchberg's Theorem 1.1. -/
theorem printedOzawaNoLocalLiftingGeneral_of_kirchberg
    (k : KirchbergKazhdanFactorizationInput.{0}) :
    PrintedOzawaNoLocalLiftingGeneral := by
  intro G _ _ _ hT hH
  haveI : Group.FG G := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT G hT
  haveI : Countable G := ContinuumMultiplicity.countable_of_fg G
  exact not_hasLocalLiftingProperty_of_not_hasFactorizationProperty G hH
    (not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan k G hT)

/-- **tex l.51–54 at 8b36733d7, closed**: the full C⋆-algebra of an infinite simple
hyperlinear group with property (T) cannot have the local lifting property. -/
theorem printedOzawaNoLocalLiftingGeneral : PrintedOzawaNoLocalLiftingGeneral :=
  printedOzawaNoLocalLiftingGeneral_of_kirchberg
    KirchbergTheorem.kirchbergKazhdanFactorizationInput.{0}

end SimpleKazhdanSofic
end GroupApproximation

open GroupApproximation.SimpleKazhdanSofic

#audit_axioms not_hasLocalLiftingProperty_of_not_hasFactorizationProperty
#audit_axioms PrintedOzawaNoLocalLiftingGeneral
#audit_axioms printedOzawaNoLocalLiftingGeneral_of_kirchberg
#audit_closed_axioms printedOzawaNoLocalLiftingGeneral
