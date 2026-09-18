import GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerForms
import GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.Leaf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fournier-Facio paragraph forms over the five open residuals

Lane gl-assembly-09.  `non_mf_groups_exist.tex`, the Fournier-Facio paragraph before the proof of
`\label{thm:torsion-free}` (census line 2160; lines 1675–1685 in older numberings):

> Fournier-Facio constructs a finitely presented torsion-free group $G_0$ with property (T), a
> subgroup $\Gamma\le G_0$ with property (T), an element $t\in G_0$ with $t\Gamma t^{-1}\le\Gamma$,
> and a subgroup $J\le G_0$ isomorphic to a finitely presented infinite simple group, such that
> $[\Gamma,J]=1$ and $tJt^{-1}\le\Gamma$ \cite[\S2]{FFF}.

Each theorem applies the matching `TorsionFreeGreendlingerForms.*_of_greendlinger`
(`TorsionFreeGreendlingerForms.lean:51-87`) to `leastAreaLeaf_of_openResidualsBelow`.  The
remaining hypothesis `hopen` is explained in `GreendlingerClosedForms/Leaf`.
-/

namespace GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms

/-- **Fournier-Facio's Proposition 2.3, the manuscript quotient field** (tex lines 1675–1680,
`\cite[\S2]{FFF}`), over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_fournierFacioQuotientStatementForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TheoremC.FournierFacioQuotientStatement :=
  TorsionFreeGreendlingerForms.fournierFacioQuotientStatement_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_fournierFacioQuotientStatementForm_of_openResidualsBelow

/-- **Hull's Corollary 7.4, in the form the Fournier-Facio paragraph uses** (tex lines 1680–1683),
over the five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_hullCommonQuotientForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TheoremC.HullCommonQuotientStatement :=
  TorsionFreeGreendlingerForms.hullCommonQuotient_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_hullCommonQuotientForm_of_openResidualsBelow

/-- **The five literature inputs of the Fournier-Facio paragraph** (tex lines 1675–1683), over the
five open residuals of the Below Greendlinger waist. -/
theorem manuscriptSentence_literatureInputsForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TheoremC.LiteratureInputs :=
  TorsionFreeGreendlingerForms.literatureInputs_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_literatureInputsForm_of_openResidualsBelow

/-- **The Fournier-Facio paragraph** (tex lines 1675–1685), over the five open residuals of the
Below Greendlinger waist. -/
theorem manuscriptSentence_fournierFacioParagraphForm_of_openResidualsBelow
    (hopen :
      GGT.VanKampen.GreendlingerLeaf.AsmWaist.GreendlingerOpenResidualsBelowStatement.{0, 0, 0}) :
    TorsionFreePrinted.FournierFacioParagraph :=
  TorsionFreeGreendlingerForms.fournierFacioParagraph_of_greendlinger
    (leastAreaLeaf_of_openResidualsBelow hopen)

#audit_axioms GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms.manuscriptSentence_fournierFacioParagraphForm_of_openResidualsBelow

end GroupApproximation.Manuscript.NonMF.GreendlingerClosedForms
