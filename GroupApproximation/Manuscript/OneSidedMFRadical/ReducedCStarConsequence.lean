import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem

/-!
# The reduced-C⋆ clause of `thm:headline`, and the Blackadar--Kirchberg MF question

`non_mf_groups_exist.tex`, abstract and Theorem `thm:headline` — "Its reduced
group C*-algebra `C*_r(H)` is separable and stably finite, but is not MF." —
together with the general step the Introduction states just before it: "For
every countable group `G`, the reduced group algebra `C*_r(G)` is separable and
has a faithful canonical trace, hence is stably finite.  If `C*_r(G)` is MF,
restricting an MF embedding to its canonical group unitaries shows that `G` is
MF.  Therefore a non-MF group automatically gives a separable stably finite
reduced group `C*`-algebra that is not MF."

Everything below is that general step applied at the manuscript's own group

`H = EL₁₂(L_{𝔽₂}(1,2))`,

whose failure of MF-ness is the last conjunct of
`HeadlineTheorem.manuscriptBinaryLeavittFullRadical`.  No analysis is done
here: separability is
`ReducedGroupCStarTrace.reducedGroupCStar_separableSpace`, stable finiteness is
`reducedGroupCStar_isStablyFiniteCStarAlgebra`, the unitary restriction is
`not_isMFAlgebra_reducedGroupCStar`, and the three are already packaged as
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`.  What this module
adds is the *shape*: three named propositions, each with every quantifier
inside the statement, so that a reader can `#check` one name against one
printed sentence.

* `ReducedCStarConsequence` — the printed clause at `H` itself.
* `SeparableStablyFiniteNonMFCStarAlgebraExists` — the same content with the
  group forgotten: some separable stably finite C⋆-algebra is not MF.
* `NotEverySeparableStablyFiniteCStarAlgebraIsMF` — the same sentence written
  as the refutation of the universal statement it denies.
* `PrintedHeadline` — the whole of `thm:headline` as printed, which is the
  clause above conjoined with the clauses proved upstream.

## Why `PrintedHeadline` exists

`RankTwelveEndpoint.HeadlineConclusion` was the exact printed theorem before
the reduced-C⋆ sentence was added to it, and it is now a proper subclaim: it
carries nontriviality, simplicity, property `(T)`, `Rad_MF(H) = H`, triviality
of every MF-target homomorphism, and failure of MF-ness, but says nothing about
`C*_r(H)`.  The printed theorem also opens with "`H` is finitely generated",
which `HeadlineConclusion` does not assert either.

`PrintedHeadline` restores both, so that the label `thm:headline` again has a
single declaration stating exactly what it prints.  It is a conjunction of
already-proved propositions and introduces no new mathematics; the reason to
name it is that a printed label with no single Lean target is a gap a reader
cannot check, not that anything further is being claimed.

This module is where the conjunction has to live: it is the first point in the
import graph at which `HeadlineConclusion` and `ReducedCStarConsequence` are
both in scope.

## Which Blackadar--Kirchberg question this answers, and which it does not

The manuscript's "Relation to prior work" subsection distinguishes two
questions, and so does this module.

* **The 1994 Oberwolfach suggestion is untouched.**  Blackadar and Kirchberg
  suggested there that every separable **nuclear** stably finite C⋆-algebra
  might be NF.  `C*_r(H)` is the reduced group C⋆-algebra of a non-amenable
  group, so it is not nuclear, and nothing here bears on that suggestion.  The
  non-amenability is proved, in `ReducedCStarNotNuclear`:
  `manuscriptRankTwelveNonNuclearityProfile` gives `Infinite H`,
  `¬ IsAmenable H` and failure of the translation-tested approximation
  property, unconditionally.  `Infinite H` there is `RankTwelve.infinite`,
  which transports `Infinite` on the coefficient ring through the elementary
  root `e₀₁`; no MF fact enters, and this module claims no other route to it.

  The step from that profile to non-nuclearity depends on which nuclearity
  predicate is meant, and the two answers differ.  At the translation-tested
  property of `Analysis.LanceNuclearity` the profile *is* the failure, so
  non-nuclearity is unconditional.  At the corpus-wide
  `CStarExactness.IsNuclearCStarAlgebra` it is not: `ReducedCStarNotNuclear`'s
  endpoint `manuscriptReducedCStarNotNuclear` carries
  `TranslationCPAPReductionInput` as a leading binder — the hard direction of
  Lance's theorem, which this repository does not prove — and is accordingly
  audited with `#audit_axioms` rather than `#audit_closed_axioms`.  So "it is
  not nuclear" above should be read as unconditional in the first sense and
  conditional in the second.  Either way it is inert here: no proposition in
  this module has a nuclearity hypothesis, and none uses one.
* **The 1997 question, and what is and is not new.**  Their 1997 paper
  introduced MF C⋆-algebras and observed that no separable stably finite
  C⋆-algebra was then known not to be MF; the question whether every separable
  stably finite C⋆-algebra is MF became known as the Blackadar--Kirchberg MF
  problem.  `NotEverySeparableStablyFiniteCStarAlgebraIsMF` is the negation of
  that universal statement, at the repository's reading of the predicates
  (`Analysis.MFAlgebra.IsMFAlgebra` and
  `Analysis.ReducedGroupCStarStablyFinite.IsStablyFiniteCStarAlgebra`).  It is
  **not** claimed here that this manuscript is what settles that question: the
  negative solution of the Connes embedding problem already produced stably
  finite non-MF C⋆-algebras in general.  The manuscript's own wording is the
  accurate one — `thm:headline` "provides such an example **among reduced
  group C⋆-algebras**" — and that is `ReducedCStarConsequence`, not the
  forgetful existential below.

## No priority is claimed for the bare existence statement

Separable stably finite C⋆-algebras that are not MF are already known: the
negative solution of the Connes embedding problem produced them in general.
`SeparableStablyFiniteNonMFCStarAlgebraExists` and
`NotEverySeparableStablyFiniteCStarAlgebraIsMF` are therefore *not* offered as
new theorems, and the manuscript does not present them as such — they are
stated here because they are the literal existential and refutation forms of
the printed sentence, and because that is the shape in which the
Blackadar--Kirchberg question is asked.  What is new in `thm:headline` is that
such an example occurs among **reduced group** C⋆-algebras, which is
`ReducedCStarConsequence`, and that is the proposition carrying the content.
No docstring in this module should be read as saying that this work settles
the Blackadar--Kirchberg MF problem.

## What "stably finite" means here

`IsStablyFiniteCStarAlgebra` is the operator-algebraic reading — every isometry
in every finite matrix amplification is a unitary — and deliberately not
mathlib's `IsStablyFiniteRing`.  The polar-decomposition argument carrying the
former to the latter *is* formalized, in
`Analysis.ReducedGroupCStarDedekindFinite`
(`IsStablyFiniteCStarAlgebra.isStablyFiniteRing`, and the instance
`reducedGroupCStar_isStablyFiniteRing` for `C*_r(G)` itself), so the printed
"stably finite" holds in both readings.  The propositions below are stated at
the operator-algebraic one because that is what the Blackadar--Kirchberg
literature means; see the docstring of `IsStablyFiniteCStarAlgebra` itself.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint
open ReducedGroupCStarTrace

/-- `H = EL₁₂(L_{𝔽₂}(1,2))` is countable.  The instance is needed both to
*state* `IsCDEOperatorMF H` and to feed the countability hypothesis of
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`; `HeadlineTheorem`
declares the same instance locally, and a `local instance` is not exported to
importing modules. -/
local instance reducedCStarCountable : Countable H :=
  RankTwelveEndpoint.countable

/-! ## The printed clause at the manuscript's group -/

/-- **The printed reduced-C⋆ clause of `thm:headline`, as one proposition.**
The concrete reduced group C⋆-algebra of `H = EL₁₂(L_{𝔽₂}(1,2))` is separable,
is stably finite, and is not an MF C⋆-algebra.

The first two conjuncts hold for every countable group and use nothing about
`H`; only the third uses the failure of MF-ness proved in `HeadlineTheorem`. -/
def ReducedCStarConsequence : Prop :=
  TopologicalSpace.SeparableSpace (ReducedGroupCStar H) ∧
    IsStablyFiniteCStarAlgebra (ReducedGroupCStar H) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar H)

/-- **The printed clause, proved, hypothesis-free.**  The single input about
`H` is the last conjunct of `manuscriptBinaryLeavittFullRadical`, namely
`¬ IsCDEOperatorMF H`; the rest is the general countable-group statement
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`.

The printed simplicity clause of `thm:headline` is used nowhere on this
route. -/
theorem manuscriptReducedCStarConsequence : ReducedCStarConsequence := by
  obtain ⟨-, -, -, -, -, -, hnot⟩ := manuscriptBinaryLeavittFullRadical
  exact reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra H hnot

/-! ## The same content with the group forgotten -/

/-- **Existence form: some separable stably finite C⋆-algebra is not MF.**

This is the shape in which the Blackadar--Kirchberg MF question is asked, and
it is deliberately weaker than `ReducedCStarConsequence`: it forgets that the
witness is a reduced group C⋆-algebra.  As the module docstring records, the
bare existence statement is not new — the negative solution of the Connes
embedding problem already supplies such algebras — and no priority is claimed
for it here.

The `CStarAlgebra` structure is bound existentially rather than left to
instance synthesis, since `A` is a bound variable; `letI` then makes it
available to the three conjuncts, which all need it. -/
def SeparableStablyFiniteNonMFCStarAlgebraExists : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    TopologicalSpace.SeparableSpace A ∧
      IsStablyFiniteCStarAlgebra A ∧ ¬ IsMFAlgebra A

/-- **The existence statement, proved.**  The witness is `C*_r(H)` with its
canonical C⋆-algebra structure `reducedGroupCStarCStarAlgebra`, and the three
conjuncts are exactly `manuscriptReducedCStarConsequence`. -/
theorem manuscriptSeparableStablyFiniteNonMFCStarAlgebraExists :
    SeparableStablyFiniteNonMFCStarAlgebraExists :=
  ⟨ReducedGroupCStar H, inferInstance, manuscriptReducedCStarConsequence⟩

/-- **Refutation form: the Blackadar--Kirchberg MF question, answered no.**  It
is not the case that every separable stably finite C⋆-algebra is MF.

This is the negation of the universal statement recorded in the manuscript's
"Relation to prior work" subsection as the Blackadar--Kirchberg MF problem.  It
carries no nuclearity hypothesis, and correspondingly says nothing about the
1994 Oberwolfach suggestion, which did carry one. -/
def NotEverySeparableStablyFiniteCStarAlgebraIsMF : Prop :=
  ¬ ∀ (A : Type) [CStarAlgebra A],
      TopologicalSpace.SeparableSpace A → IsStablyFiniteCStarAlgebra A →
        IsMFAlgebra A

/-- **The universal statement is false.**  Instantiating it at `C*_r(H)`, whose
separability and stable finiteness are the first two conjuncts of
`manuscriptReducedCStarConsequence`, contradicts its third. -/
theorem manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMF :
    NotEverySeparableStablyFiniteCStarAlgebraIsMF := by
  intro hall
  obtain ⟨hsep, hsf, hnot⟩ := manuscriptReducedCStarConsequence
  exact hnot (hall (ReducedGroupCStar H) hsep hsf)

/-! ## The printed theorem, whole -/

/-- **`thm:headline` exactly as printed, as one proposition.**  With
`R = L_{𝔽₂}(1,2)` and `H = EL₁₂(R)`: `H` is finitely generated, nontrivial,
simple, has
property `(T)`, and `Rad_MF(H) = H` — equivalently every homomorphism from `H`
to an MF group is trivial, so in particular `H` is not MF — and its reduced
group C⋆-algebra `C*_r(H)` is separable and stably finite but is not MF.

The three conjuncts are, in order, finite generation, the six clauses of
`RankTwelveEndpoint.HeadlineConclusion`, and the reduced-C⋆ clause
`ReducedCStarConsequence`.  Finite generation is a separate conjunct because
`HeadlineConclusion` does not carry it, though the printed sentence states it
first; the reduced-C⋆ clause is separate because `HeadlineConclusion` predates
it.  Nothing here is proved that was not already proved upstream — see the
module docstring for why the conjunction is nevertheless worth a name. -/
def PrintedHeadline : Prop :=
  Group.FG H ∧ HeadlineConclusion ∧ ReducedCStarConsequence

/-- **The printed theorem, proved, hypothesis-free.**  Each conjunct is
discharged by the endpoint that already owns it:
`RankTwelveEndpoint.finitelyGenerated`,
`manuscriptBinaryLeavittHeadline` — which is where simplicity enters, via
`RankTwelveEndpoint.manuscriptPropositionSimple` — and
`manuscriptReducedCStarConsequence`. -/
theorem manuscriptPrintedHeadline : PrintedHeadline :=
  ⟨RankTwelveEndpoint.finitelyGenerated, manuscriptBinaryLeavittHeadline,
    manuscriptReducedCStarConsequence⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
