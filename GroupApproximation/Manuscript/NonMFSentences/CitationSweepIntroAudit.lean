import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Manuscript.NonMF.PriorWorkConnesEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed-axiom certificates for three cited Introduction sentences

The literature-input sweep of `non_mf_groups_exist.tex`, lines 1--1337, found three
sentence carriers whose statements have no binders but whose own modules audit them
only with `#audit_axioms`.  This module certifies each one with `#audit_closed_axioms`,
so the cited results these sentences rely on are recorded as proved, not assumed.

* Census row `2a97fb901bad`, tex 284--286: "Since $W_0$ is a direct limit of residually
  finite groups, it is MF~\cite[Corollary~10 and Proposition~13]{Korchagin}."
  Carrier `AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF`.  It is proved through
  `isOperatorMF_of_isLEF` and `isLEF_of_locallyResiduallyFinite`.
* Census row `cd3ea932e46a`, tex 286--288: "So MF groups are not closed under semidirect
  products with $\mathbb Z$, which answers a question of
  Korchagin~\cite[remark following Proposition~12]{Korchagin}."
  Carrier `AmenableTraceTheorem.manuscriptMFNotClosedUnderIntSemidirect`.
* Census row `abfcbcb3af2b`, tex 328--332: "The MF problem itself was answered negatively
  in 2020: the failure of the Connes embedding problem~\cite{MIPRE} yields a
  $\mathrm{II}_1$ factor that embeds in no norm ultraproduct of matrix algebras, hence a
  separable stably finite $C^*$-algebra that is not MF~\cite[Proposition~6.1 and
  Remark~6.2]{GoldbringHart}."
  Carrier `NonMF.PriorWork.printedNegativeConnesEmbeddingSentence`.  It proves the
  conclusion through the paper's own reduced group algebra; the Connes-embedding route
  is credited context that no proof consumes.
-/

#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF
#audit_closed_axioms GroupApproximation.AmenableTraceTheorem.manuscriptMFNotClosedUnderIntSemidirect
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.PriorWork.printedNegativeConnesEmbeddingSentence
