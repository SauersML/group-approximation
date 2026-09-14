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
| 1847–1849 | Φ = [(φ_n)] is a unital *-homomorphism into Q_d | 0fbd72617dcb | formalized | `FactorizationTraceCoronaProof.manuscriptSentence_unitalStarHom`, `coronaMap`, `coronaMap_one` (360f72771); earlier `ShulmanTrace.MFTraceModel.coronaHom` | PASS; the unital clause is now stated |
| 1849–1851 | Φ(u_g)=1 ⇒ ‖φ_n(u_g)−1‖→0 ⇒ tr→1, while tr→τ_G(u_g); so g=1 | 1c2804634e53 | formalized | `FactorizationTraceCoronaProof.manuscriptSentence_generatorKernel` (360f72771); earlier `ShulmanTrace.exists_injective_coronaUnitaryHom` | PASS along the printed limit chain |
| 1851–1853 | g ↦ Φ(u_g) injective corona homomorphism ⇒ G MF, contradiction | 53f02dc594db | formalized | `FactorizationTraceCoronaProof.manuscriptSentence_injectiveCoronaHom`, `generatorCoronaHom_apply`, `manuscriptSentence_isOperatorMF`, `printedFactorizationTraceCoronaProof` (360f72771) | PASS; endpoint closed at countable G |
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
  tex 1845–1853 is the corona route. The census rows already record this (note of 0fbd72617dcb, corrected per the lead
  on 09-08), and no census row names the four stale carriers. This is stale prose, not a soundness defect. The module
  is root-imported and unowned, so a docstring fix needs its own probe; not done here.

## Landed

- `GroupApproximation/Manuscript/NonMFSentences/FactorizationTraceCoronaProof.lean`, LANDED 360f72771 (probe
  0913-172959-67907 GREEN, BUILT; build log shows [propext, Classical.choice, Quot.sound] for all five audited
  declarations and no `sorryAx`, error or warning line). Queued in `wire-queue.txt`.
  - `coronaMap M` is Φ, built from the quasidiagonal models through the theorem `ucpContractive`; `coronaMap_one`.
  - `manuscriptSentence_unitalStarHom`: value at a, multiplicativity, adjoints, unitality (tex 1847–1849).
  - `manuscriptSentence_generatorKernel`: Φ(u_g) = 1 ⇒ ‖φ_n(u_g) − 1‖ → 0 ⇒ tr → 1, the trace clause, g = 1
    (tex 1849–1851).
  - `generatorCoronaHom`, `generatorCoronaHom_apply`, `manuscriptSentence_injectiveCoronaHom`,
    `manuscriptSentence_isOperatorMF` (tex 1851–1853).
  - Closed endpoint `PrintedFactorizationTraceCoronaProof`, at countable G, the printed generality.
  - Also `exists_models_card_pos`: it discards the finitely many empty models, which is the printed `d_n ≥ 1`.
- Census rows 0fbd72617dcb, 1c2804634e53 and 53f02dc594db are re-pointed in `metadata/nm-census-rows/ms-traces-1.tsv`.
  The earlier root-reachable carriers stay listed until the module is wired.

## Range status

Every sentence of tex 1808–1858 is carried by a closed declaration or classified honestly: two attribution rows, five
definition rows, and six formalized rows (the theorem row covers two sentences). The only item outstanding is the root
wiring of 360f72771.

## Item (main, 09-14 ~10:50): contact-map part (2), empty nondegenerate small faces

Split off from ms-intro-2's `OsinLemma94ContactMapNondegenerateSmallFacesInput` (8677b0dcd). The statement agreed with
ms-intro-2 is `OsinLemma94ContactMapEmptyTwoGonInput` in `Estimating/OsinLemma94ContactMapHolds` (9e45690bc):
the faces that are nondegenerate, small and hold no object number at most `K * Delta.rCellCount`.

Hand model tests (before any Lean):
- Configuration C refutes the earlier False form. A region x runs from a to b, flanked by polygons f and f′ with a third
  neighbour each. The face (f, a, f′, b) is empty and nondegenerate, and no merge applies: every chord of f from its
  a-arc to its b-arc is longer than ε.
- Charge to regions. An empty face holds a selected region, or its polygon f makes a direct step from a to b. Regions
  number at most 12n: the binder `S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)` with
  `SectionCuts.count_le`. The charge is injective by face classes (`faceOf_eq_of_faceClass_of_componentOf`); on C and
  its mirror, one face holds one region.
- b the exterior, with regions to several sections: charge to any region inside. The Φ′_M corner count is not needed.
- No region inside: f's sector has no short side, so there is a direct object step inside F. That step is charged to
  the named input `OsinLemma94ObjectTouchComponentsInput` (ms-traces-3 proves it). Routing through
  `OsinLemma94ContactTransitionInput` would be circular.

CLAIM `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ObjectTouchComponents.lean`
- the statement only: `OsinLemma94RealizedPolygons.IsDirectStep`, `directSteps`, and `OsinLemma94ObjectTouchComponentsInput`.

CLAIM `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94ContactEmptyTwoGon.lean`
- `osinLemma94ContactMapEmptyTwoGonInput_of_objectTouch` proves ms-intro-2's count form from the touch input.
