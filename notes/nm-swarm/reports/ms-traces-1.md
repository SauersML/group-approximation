# Lane ms-traces-1: tex 1808–1858 (sec:amenable-nonqd opening, thm:factorization-nonmf-trace)

Lead: session nonsofic-existence-49, wave 2. Snapshot origin/main 61363f1b9; the tex is unchanged since 68481e4d7.

CLAIM corona-route proof sentences of thm:factorization-nonmf-trace GroupApproximation/Manuscript/NonMFSentences/FactorizationTraceCoronaProof.lean

## Ledger

Keys are from `metadata/NON_MF_SENTENCE_CENSUS.tsv`, matched by text; its line numbers are at the pre-chain-core hash.

| tex | sentence | key | status | carriers | verdict |
|---|---|---|---|---|---|
| 1812–1814 | Brown observed that amenable ⇒ quasidiagonal was unknown | 2acc03ce92d4 | attribution | — | honest |
| 1814–1815 | "we use the sequential form of his definitions" | e66fc0145639 | attribution | — | honest; the definitions are the next two rows |
| 1815–1823 | amenable trace | 4daee6130a7d | definition | `Quasidiagonal.IsAmenableTrace`, `AmenableTraceModel` | PASS |
| 1824–1825 | quasidiagonal trace | f02bfca27b23 | definition | `Quasidiagonal.IsQuasidiagonalTrace`, `QuasidiagonalTraceModel` | PASS |
| 1827–1828 | canonical unitary `u_g` | ca353970e9e3 | definition | `maximalGroupCStarGenerator` | PASS |
| 1828–1832 | canonical trace `τ_G` | c9da12b3f699 | definition | `canonicalMaximalTrace_generator_one`, `canonicalMaximalTrace_generator_of_ne_one` | PASS |
| 1836–1837 | G not MF ⇒ τ_G not quasidiagonal | 01d34ed18b0a | formalized | `NinetyNineProblems.manuscriptCanonicalMaximalTraceNotIsQuasidiagonalTraceOfNotIsOperatorMF` | PASS |
| 1837–1839 | amenable ⇒ amenable and not quasidiagonal | 01d34ed18b0a | formalized | `canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF` | PASS |
| 1845–1846 | suppose τ_G quasidiagonal, with u.c.p. maps | fa19477760b9 | formalized | `FactorizationTraceSentences.manuscriptSentence_quasidiagonalModel` | PASS in content; its docstring quotes superseded wording (F1) |
| 1847–1849 | Φ = [(φ_n)] is a unital *-homomorphism into Q_d | 0fbd72617dcb | formalized | `ShulmanTrace.MFTraceModel.coronaHom` | GAP: the carrier is the non-unital *-hom of an MF trace model; the printed "unital" clause is not stated |
| 1849–1851 | Φ(u_g)=1 ⇒ ‖φ_n(u_g)−1‖→0 ⇒ tr→1, while tr→τ_G(u_g); so g=1 | 1c2804634e53 | formalized | `ShulmanTrace.exists_injective_coronaUnitaryHom` | GAP: the step is buried in that proof, which compares Φ(u_g) with Φ(1) through `eq_of_coronaHom_eq` after a unitary correction |
| 1851–1853 | g ↦ Φ(u_g) injective corona homomorphism ⇒ G MF, contradiction | 53f02dc594db | formalized | `exists_injective_coronaUnitaryHom`, `FactorizationTraceSentences.manuscriptSentence_quasidiagonalGivesMF` | PARTIAL ROUTE: MF is reached through the MF-trace wrapper |
| 1856–1857 | locally residually finite | a817c6ae86c9 | definition | `LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite` | PASS |

## Checks behind the PASS rows

- Definitions: models are linear, unital and completely positive (the predicate includes the real-form clause added
  2026-08-19). The multiplicative clause is in normalized Hilbert–Schmidt norm (amenable) or operator norm
  (quasidiagonal), and the trace clause is identical. Empty models are allowed, which only weakens both predicates:
  the trace clause at 1 forces all but finitely many models to be nonempty (`MFTraceModel.eventually_card_pos`).
- Theorem: closed (`#audit_closed_axioms` at `Manuscript/NonMF/Audit/Sec4.lean:83`) and root-imported. It is stated for
  every group (the printed statement has countable G). `IsOperatorMF` is the printed MF notion by
  `isCDEOperatorMF_iff_isOperatorMF` (`Sofic/CDEOperatorMF.lean:36`) and `manuscriptIntroductionMFDefinition`.
- No literature binder: `isMFTrace_of_isQuasidiagonalTrace` takes `Quasidiagonal.ucpContractive` (a theorem) and a
  tracial-state proof, and `isOperatorMF_of_isMFTrace_canonicalMaximal` takes only the MF trace. The conditional
  baseline has no finding in these namespaces.
- `IsLocallyResiduallyFinite` is `∀ H : Subgroup N, H.FG → Group.ResiduallyFinite ↑H`. Its module is root-reachable
  through `Analysis.LocallyRFQuasidiagonalTrace`.

## Findings

- F1: `Manuscript/OneSidedMFRadical/FactorizationTraceSentences.lean` (last touched at the restore commit 3f71a3a50)
  quotes a six-sentence polar-decomposition proof that is no longer printed. `manuscriptSentence_nearIsometry`,
  `_unitalAtIdentity`, `_traceTendsToZero` and `_lastAssertion` carry sentences that are gone. The printed proof at
  tex 1845–1853 is the corona route. This is stale prose, not a soundness defect.

## Building

- Claimed module: carriers for tex 1847–1853 along the printed corona route. Φ is built from the quasidiagonal models
  and is unital. Φ(u_g) = 1 gives operator-norm-null deviations, the normalized traces tend to 1, and g = 1. The
  resulting homomorphism into the corona unitaries is injective, so G is operator MF. The closed endpoint
  `PrintedFactorizationTraceCoronaProof` holds at the printed countable generality.
- After landing, rows 0fbd72617dcb, 1c2804634e53 and 53f02dc594db are re-pointed in
  `metadata/nm-census-rows/ms-traces-1.tsv`.
