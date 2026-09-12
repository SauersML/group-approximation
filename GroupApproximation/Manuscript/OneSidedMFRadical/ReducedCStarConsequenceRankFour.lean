import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Analysis.StrictCompressionFromPrinted
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheoremRankFour

/-!
# The two C⋆ clauses of `thm:headline` at rank four, and the printed theorem

`non_mf_groups_exist.tex`, abstract and Theorem `thm:headline` — "So `H` is not
MF, and `C*_r(H)` is separable and stably finite but not MF, while
`C*_max(H)` is not finite: it contains a proper isometry." — together with the
general step the Introduction states just before it: "For every countable group
`G`, the reduced group algebra `C*_r(G)` is separable and has a faithful
canonical trace, hence is stably finite.  If `C*_r(G)` is MF, restricting an MF
embedding to its canonical group unitaries shows that `G` is MF.  Therefore a
non-MF group automatically gives a separable stably finite reduced group
`C*`-algebra that is not MF."

Everything below is that step, and the maximal-C⋆ remark, applied at the
manuscript's own group

`H = EL₄(L_{𝔽₂}(1,2))`.

No analysis is done here.  Separability is
`ReducedGroupCStarTrace.reducedGroupCStar_separableSpace`, stable finiteness is
`reducedGroupCStar_isStablyFiniteCStarAlgebra`, the unitary restriction is
`not_isMFAlgebra_reducedGroupCStar`, and the three are already packaged as
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`; the maximal-C⋆
clause is `MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses`
at the printed strict compression `uLu⁻¹ ⊊ L` of `RankFourConfiguration`.
What this module adds is the *shape*: named propositions, each with every
quantifier inside the statement, so that a reader can `#check` one name against
one printed sentence.

* `ReducedCStarConsequenceRankFour` — the reduced-C⋆ clause at `H` itself.
* `MaximalCStarNotFiniteRankFour` — the maximal-C⋆ clause at `H` itself.
* `SeparableStablyFiniteNonMFCStarAlgebraExistsRankFour` — the same reduced-C⋆
  content with the group forgotten.
* `NotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour` — the same sentence
  written as the refutation of the universal statement it denies.
* `PrintedHeadlineRankFour` — the whole of `thm:headline` as printed.

## What `PrintedHeadlineRankFour` fixes

`RankFourEndpoint.HeadlineConclusion` carries nontriviality, simplicity,
property `(T)`, `Rad_MF(H) = H`, triviality of every MF-target homomorphism,
and failure of MF-ness, but says nothing about `C*_r(H)` or `C*_max(H)`, and it
does not carry the finite generation the printed theorem states first.
`PrintedHeadlineRankFour` restores all four, so that the label `thm:headline`
has a single declaration stating exactly what it prints.

The maximal-C⋆ conjunct is the one the superseded rank-twelve package left out:
`RankTwelveEndpoint`'s headline stopped at the reduced-C⋆ sentence even after
the printed theorem had grown a maximal-C⋆ sentence, and the strictness input
it needed lived in a separate module that the headline did not import.  Here it
is a conjunct of the printed proposition.

## Which Blackadar--Kirchberg question this answers, and which it does not

The manuscript's "Relation to prior work" subsection distinguishes two
questions, and so does this module.

* **The 1994 Oberwolfach suggestion is untouched.**  Blackadar and Kirchberg
  suggested there that every separable **nuclear** stably finite C⋆-algebra
  might be NF.  `C*_r(H)` is the reduced group C⋆-algebra of a non-amenable
  group, so it is not nuclear, and nothing here bears on that suggestion.  No
  proposition in this module has a nuclearity hypothesis, and none uses one.
* **The 1997 question, and what is and is not new.**  Their 1997 paper
  introduced MF C⋆-algebras and observed that no separable stably finite
  C⋆-algebra was then known not to be MF; the question whether every separable
  stably finite C⋆-algebra is MF became known as the Blackadar--Kirchberg MF
  problem.  `NotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour` is the
  negation of that universal statement, at the repository's reading of the
  predicates (`Analysis.MFAlgebra.IsMFAlgebra` and
  `Analysis.ReducedGroupCStarStablyFinite.IsStablyFiniteCStarAlgebra`).  It is
  **not** claimed here that this manuscript is what settles that question: the
  negative solution of the Connes embedding problem already produced stably
  finite non-MF C⋆-algebras in general.  The manuscript's own wording is the
  accurate one — `thm:headline` provides such an example **among reduced group
  C⋆-algebras** — and that is `ReducedCStarConsequenceRankFour`, not the
  forgetful existential below.

## What "stably finite" means here

`IsStablyFiniteCStarAlgebra` is the operator-algebraic reading — every isometry
in every finite matrix amplification is a unitary — and deliberately not
mathlib's `IsStablyFiniteRing`.  The polar-decomposition argument carrying the
former to the latter *is* formalized, in
`Analysis.ReducedGroupCStarDedekindFinite`, so the printed "stably finite"
holds in both readings.  The reduced-C⋆ proposition below is stated at the
operator-algebraic one because that is what the Blackadar--Kirchberg
literature means; the maximal-C⋆ proposition is stated at both, because what it
denies is finiteness and both denials are available.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankFourEndpoint
open ReducedGroupCStarTrace

/-- `H = EL₄(L_{𝔽₂}(1,2))` is countable.  The instance is needed both to
*state* `IsCDEOperatorMF H` and to feed the countability hypothesis of
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`;
`HeadlineTheoremRankFour` declares the same instance locally, and a
`local instance` is not exported to importing modules. -/
local instance reducedCStarCountableRankFour : Countable H :=
  RankFourEndpoint.countable

/-! ## The reduced-C⋆ clause at the manuscript's group -/

/-- **The printed reduced-C⋆ clause of `thm:headline`, as one proposition.**
The concrete reduced group C⋆-algebra of `H = EL₄(L_{𝔽₂}(1,2))` is separable,
is stably finite, and is not an MF C⋆-algebra.

The first two conjuncts hold for every countable group and use nothing about
`H`; only the third uses the failure of MF-ness proved in
`HeadlineTheoremRankFour`. -/
def ReducedCStarConsequenceRankFour : Prop :=
  TopologicalSpace.SeparableSpace (ReducedGroupCStar H) ∧
    IsStablyFiniteCStarAlgebra (ReducedGroupCStar H) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar H)

/-- **The printed clause, proved, hypothesis-free.**  The single input about
`H` is the last conjunct of `manuscriptBinaryLeavittFullRadicalRankFour`,
namely `¬ IsCDEOperatorMF H`; the rest is the general countable-group statement
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`.

The printed simplicity clause of `thm:headline` is used nowhere on this
route. -/
theorem manuscriptReducedCStarConsequenceRankFour :
    ReducedCStarConsequenceRankFour := by
  obtain ⟨-, -, -, -, -, -, hnot⟩ := manuscriptBinaryLeavittFullRadicalRankFour
  exact reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra H hnot

/-! ## The maximal-C⋆ clause at the manuscript's group -/

/-- **The printed maximal-C⋆ clause of `thm:headline`, as one proposition.**
"while `C*_max(H)` is not finite: it contains a proper isometry."

The proper isometry is the projection `P` of the first conjunct: `P` is a
projection that the unitary of the printed compressor `u` moves strictly, and
`uPu*` dominates and is dominated by `P` in the two one-sided senses displayed.
The second and third conjuncts are the failure of finiteness that the printed
sentence draws from it, in both readings of "finite". -/
def MaximalCStarNotFiniteRankFour : Prop :=
  (∃ P : MaximalGroupCStar H,
      IsSelfAdjoint P ∧
      P * P = P ∧
      (maximalGroupCStarGenerator H u * P *
          star (maximalGroupCStarGenerator H u)) * P = P ∧
      P * (maximalGroupCStarGenerator H u * P *
          star (maximalGroupCStarGenerator H u)) = P ∧
      maximalGroupCStarGenerator H u * P *
          star (maximalGroupCStarGenerator H u) ≠ P) ∧
    ¬ IsDedekindFiniteMonoid (MaximalGroupCStar H) ∧
    ¬ IsStablyFiniteRing (MaximalGroupCStar H)

/-- **The printed maximal-C⋆ clause, proved, hypothesis-free.**  This is
`prop:max-infinite` applied to `L ≤ H` and the printed compressor `u`, through
`manuscriptMaximalCStarRemarkFromPrintedHypotheses`.  Its two inputs are
property `(T)` for the corner and the *strict* compression `uLu⁻¹ ⊊ L`, and
both are closed: `RankFourEndpoint.corner_hasKazhdanPropertyT` and
`RankFourEndpoint.u_conj_corner_lt`. -/
theorem manuscriptMaximalCStarNotFiniteRankFour :
    MaximalCStarNotFiniteRankFour := by
  have hrem :=
    MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses
      H corner u corner_hasKazhdanPropertyT u_conj_corner_lt
  exact ⟨hrem.1, hrem.2.1, hrem.2.2.1⟩

/-! ## The reduced-C⋆ content with the group forgotten -/

/-- **Existence form: some separable stably finite C⋆-algebra is not MF.**

This is the shape in which the Blackadar--Kirchberg MF question is asked, and
it is deliberately weaker than `ReducedCStarConsequenceRankFour`: it forgets
that the witness is a reduced group C⋆-algebra.  As the module docstring
records, the bare existence statement is not new — the negative solution of the
Connes embedding problem already supplies such algebras — and no priority is
claimed for it here.

The `CStarAlgebra` structure is bound existentially rather than left to
instance synthesis, since `A` is a bound variable; `letI` then makes it
available to the three conjuncts, which all need it. -/
def SeparableStablyFiniteNonMFCStarAlgebraExistsRankFour : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    TopologicalSpace.SeparableSpace A ∧
      IsStablyFiniteCStarAlgebra A ∧ ¬ IsMFAlgebra A

/-- **The existence statement, proved.**  The witness is `C*_r(H)` with its
canonical C⋆-algebra structure, and the three conjuncts are exactly
`manuscriptReducedCStarConsequenceRankFour`. -/
theorem manuscriptSeparableStablyFiniteNonMFCStarAlgebraExistsRankFour :
    SeparableStablyFiniteNonMFCStarAlgebraExistsRankFour :=
  ⟨ReducedGroupCStar H, inferInstance, manuscriptReducedCStarConsequenceRankFour⟩

/-- **Refutation form: the Blackadar--Kirchberg MF question, answered no.**  It
is not the case that every separable stably finite C⋆-algebra is MF.

This is the negation of the universal statement recorded in the manuscript's
"Relation to prior work" subsection as the Blackadar--Kirchberg MF problem.  It
carries no nuclearity hypothesis, and correspondingly says nothing about the
1994 Oberwolfach suggestion, which did carry one. -/
def NotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour : Prop :=
  ¬ ∀ (A : Type) [CStarAlgebra A],
      TopologicalSpace.SeparableSpace A → IsStablyFiniteCStarAlgebra A →
        IsMFAlgebra A

/-- **The universal statement is false.**  Instantiating it at `C*_r(H)`, whose
separability and stable finiteness are the first two conjuncts of
`manuscriptReducedCStarConsequenceRankFour`, contradicts its third. -/
theorem manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour :
    NotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour := by
  intro hall
  obtain ⟨hsep, hsf, hnot⟩ := manuscriptReducedCStarConsequenceRankFour
  exact hnot (hall (ReducedGroupCStar H) hsep hsf)

/-! ## The printed theorem, whole -/

/-- **`thm:headline` exactly as printed, as one proposition.**  With
`R = L_{𝔽₂}(1,2)` and `H = EL₄(R)`: `H` is finitely generated, nontrivial,
simple, has property `(T)`, and every homomorphism from `H` to an MF group is
trivial — so `H` is not MF — and its reduced group C⋆-algebra `C*_r(H)` is
separable and stably finite but not MF, while `C*_max(H)` is not finite: it
contains a proper isometry.

The four conjuncts are, in order, finite generation, the six clauses of
`RankFourEndpoint.HeadlineConclusion`, the reduced-C⋆ clause, and the
maximal-C⋆ clause.  Nothing here is proved that was not already proved
upstream; the reason to name it is that a printed label with no single Lean
target is a gap a reader cannot check. -/
def PrintedHeadlineRankFour : Prop :=
  Group.FG H ∧
    HeadlineConclusion ∧
    ReducedCStarConsequenceRankFour ∧
    MaximalCStarNotFiniteRankFour

/-- **The printed theorem, proved, hypothesis-free.**  Each conjunct is
discharged by the endpoint that already owns it:
`RankFourEndpoint.finitelyGenerated`,
`manuscriptBinaryLeavittHeadlineRankFour` — which is where simplicity enters,
via `RankFourEndpoint.manuscriptPropositionSimple` —
`manuscriptReducedCStarConsequenceRankFour`, and
`manuscriptMaximalCStarNotFiniteRankFour`. -/
theorem manuscriptPrintedHeadlineRankFour : PrintedHeadlineRankFour :=
  ⟨RankFourEndpoint.finitelyGenerated, manuscriptBinaryLeavittHeadlineRankFour,
    manuscriptReducedCStarConsequenceRankFour,
    manuscriptMaximalCStarNotFiniteRankFour⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
