import GroupApproximation.GGT.OsinLemma71Printed
import GroupApproximation.GGT.AcylindricallyHyperbolicOsin
import GroupApproximation.Manuscript.NonMF.OsinTheorem12NonDegenerate
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# The two printed sentences that cite Osin, each as one closed proposition

`non_mf_groups_exist.tex` cites *Acylindrically hyperbolic groups* twice, in two
proof sentences of `sec:torsion-free`.  Both citations are already theorems of
this repository:

* Osin's Lemma 7.1, in the case `lem:saturation` uses it, is
  `GGT.OsinPrinted.osinLemma71Printed` (`GGT/OsinLemma71Printed.lean`);
* Osin's Theorem 1.2, `(AH₁) ⇒ (AH₄)`, is
  `TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded`
  (`Manuscript/NonMF/OsinTheorem12NonDegenerate.lean`).

The census rows for the two sentences name two carriers each, one per clause.
This module states each **whole printed sentence** as one named `Prop` and proves
it with no hypothesis, so a row can name a single closed endpoint.

## `lem:saturation`, proof, first sentence (tex lines 1659–1662)

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1]; since
> `G` is torsion-free, `N` normalizes no nontrivial finite subgroup, so `N` is
> suitable.

`SaturationSuitableSentence` carries all four conclusions: `N` is infinite, `N`
acts non-elementarily on `Γ(G,A)`, `N` normalizes no nontrivial finite subgroup,
and `N` is suitable.  `A` is the manuscript's generating set from Hull's
Theorem 3.12, bundled as `HullGeneratingSet`.  The sentence uses only that `G` is
torsion-free and that `N` is normal and nontrivial, so the proposition is stated
at those hypotheses; the lemma's other hypotheses on `G` are not needed.

## `cor:regular-nonmf-algebra`, proof, first sentence (tex lines 1725–1728)

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]
> and has no nontrivial finite normal subgroup.

`AlgebraOsinSentence` states it with Hull's Cayley-graph notion
`TorsionFree.IsAcylindricallyHyperbolic`, and `AlgebraOsinSentenceOsin` with
Osin's own notion `GGT.IsAcylindricallyHyperbolicOsin`, a non-elementary
acylindrical isometric action on a geodesic hyperbolic space.  The manuscript does
not define *acylindrically hyperbolic*; the second form is the notion Osin's paper
uses, and `GGT.isAcylindricallyHyperbolic_of_osin` passes from it to the first.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace OsinCitedSentences

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

/-! ## `lem:saturation`: Osin, Lemma 7.1 -/

/-- **`lem:saturation`, the printed sentence citing Osin [Lemma 7.1]**, whole.

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1]; since
> `G` is torsion-free, `N` normalizes no nontrivial finite subgroup, so `N` is
> suitable. -/
def SaturationSuitableSentence : Prop :=
  ∀ {G : Type} [Group G] (A : HullGeneratingSet G), IsPowerTorsionFree G →
    ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ →
      (N : Set G).Infinite ∧ ActsNonElementarily N (Cayley.base A.alphabet) ∧
        HullSuitable.NormalizesNoNontrivialFinite N ∧ Suitable A.alphabet N

/-- **The saturation sentence, closed.**  The first two clauses are
`GGT.OsinPrinted.manuscriptSentence_saturationOsinClosed`, which proves Osin's
Lemma 7.1 in the printed case; the last two are
`TorsionFreePrintedSentences.manuscriptSentence_saturationSuitable`. -/
theorem manuscriptSentence_saturationSuitableClosed : SaturationSuitableSentence := by
  intro G _ A htf N _ hN
  obtain ⟨hinf, hne⟩ :=
    GGT.OsinPrinted.manuscriptSentence_saturationOsinClosed.{0} A htf N hN
  obtain ⟨hnf, hsuit⟩ :=
    TorsionFreePrintedSentences.manuscriptSentence_saturationSuitable htf hne
  exact ⟨hinf, hne, hnf, hsuit⟩

#audit_closed_axioms manuscriptSentence_saturationSuitableClosed

/-! ## `cor:regular-nonmf-algebra`: Osin, Theorem 1.2 -/

/-- **`cor:regular-nonmf-algebra`, the printed sentence citing Osin [Theorem 1.2]**,
whole, with Hull's Cayley-graph notion of acylindrical hyperbolicity.

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]
> and has no nontrivial finite normal subgroup. -/
def AlgebraOsinSentence : Prop :=
  ∀ (Q : Type) [Group Q] [Countable Q], IsPowerTorsionFree Q →
    IsAcylindricallyHyperbolic Q →
      (∃ E : Subgroup Q, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded Q E) ∧
        HasTrivialFiniteRadical Q

/-- **The algebra sentence, closed.**  The first clause is Osin's Theorem 1.2,
`TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded`; the second is
`TorsionFreePrintedSentences.manuscriptSentence_algebraTrivialFiniteRadical`. -/
theorem manuscriptSentence_algebraOsinClosed : AlgebraOsinSentence := by
  intro Q _ _ htf hah
  exact ⟨@TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded Q _ hah,
    TorsionFreePrintedSentences.manuscriptSentence_algebraTrivialFiniteRadical htf⟩

#audit_closed_axioms manuscriptSentence_algebraOsinClosed

/-- **The same printed sentence, with Osin's notion of acylindrical hyperbolicity**:
`Q` admits a non-elementary acylindrical isometric action on a geodesic hyperbolic
space.

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]
> and has no nontrivial finite normal subgroup. -/
def AlgebraOsinSentenceOsin : Prop :=
  ∀ (Q : Type) [Group Q] [Countable Q], IsPowerTorsionFree Q →
    GGT.IsAcylindricallyHyperbolicOsin Q →
      (∃ E : Subgroup Q, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded Q E) ∧
        HasTrivialFiniteRadical Q

/-- **The algebra sentence in Osin's notion, closed.**  Osin's notion gives Hull's
by `GGT.isAcylindricallyHyperbolic_of_osin`, and then
`manuscriptSentence_algebraOsinClosed` applies. -/
theorem manuscriptSentence_algebraOsinClosedOsin : AlgebraOsinSentenceOsin := by
  intro Q _ _ htf hah
  exact manuscriptSentence_algebraOsinClosed Q htf
    (GGT.isAcylindricallyHyperbolic_of_osin hah)

#audit_closed_axioms manuscriptSentence_algebraOsinClosedOsin

end OsinCitedSentences
end NonMF
end Manuscript
end GroupApproximation
