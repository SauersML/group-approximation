import GroupApproximation.Dynamics.InvolutionLocalizationRingClosed
import GroupApproximation.Dynamics.InvolutionLocalizationMatrix
import GroupApproximation.Dynamics.CoreKernelFTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`: the printed lemma

`non_mf_groups_exist.tex`, `\label{lem:involution-localization}` (tex 1663–1670):

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and
> $J=p_CIp_C$.  Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with
> $w-1\in I$, $w^2=1$, and $wFw^{-1}\subset J$.  Over $\F_2$, every finite subset of $K_n(I)$ is
> simultaneously conjugate into the unitized $K_n(J)$ by $wI_n$; for $n\ge2$ this involution lies
> in $\EL_n(R_X)$.

The two clauses compose as follows:

* the finite-field clause is closed: `involutionLocalizationRingClause_closed`
  (InvolutionLocalizationRingClosed);
* the `F₂` clause follows from it and `CoreKernelElementaryStatement`:
  `involutionLocalizationMatrixClause_of_ringClause` (InvolutionLocalizationMatrix);
* `CoreKernelElementaryStatement`, the finite matrix argument of thm:core-mf-radical, follows from the
  local matriciality of the transient ideal over `F₂`: `coreKernelElementaryStatement_of_matricial`
  (CoreKernelFTwo).

So the printed lemma rests on one statement, `TransientIdealLocallyMatricialFTwoStatement`, the `F₂`
form of the local matriciality in lem:transient-matrices (owner chain-matricial).

* `printedInvolutionLocalization_of_coreKernelElementary`;
* `printedInvolutionLocalization_of_matricial`.
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

/-- **lem:involution-localization** (tex 1663–1670), over the finite matrix argument of
thm:core-mf-radical. -/
theorem printedInvolutionLocalization_of_coreKernelElementary
    (hel : CoreKernelElementaryStatement) : PrintedInvolutionLocalization :=
  ⟨involutionLocalizationRingClause_closed,
    involutionLocalizationMatrixClause_of_ringClause involutionLocalizationRingClause_closed hel⟩

/-- **lem:involution-localization** (tex 1663–1670), over the local matriciality of the transient
ideal over `F₂` (lem:transient-matrices). -/
theorem printedInvolutionLocalization_of_matricial
    (h : TransientIdealLocallyMatricialFTwoStatement) : PrintedInvolutionLocalization :=
  printedInvolutionLocalization_of_coreKernelElementary (coreKernelElementaryStatement_of_matricial h)

end ClopenCrossedProduct

end GroupApproximation

#audit_axioms GroupApproximation.ClopenCrossedProduct.printedInvolutionLocalization_of_coreKernelElementary
#audit_axioms GroupApproximation.ClopenCrossedProduct.printedInvolutionLocalization_of_matricial
