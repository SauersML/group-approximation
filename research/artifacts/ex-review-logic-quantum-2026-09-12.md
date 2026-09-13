# EX review: logic, complexity, quantum and unified-theory lanes (2026-09-12)

Lane `ex-verify-logic-quantum`, adversarial verifier of the EX swarm.  One section per checked
claim or route.  Long sections go to part files
`research/artifacts/ex-review-logic-quantum-2026-09-12-part<N>.md`, indexed at the end of this file.

## 0. Scope and method

Lanes under review: ex-complexity-sofic, ex-complexity-amenable, ex-complexity-sofic-amplifier,
ex-ugc, ex-ugc-rounding-pgroups, ex-quantum-pcp, ex-nh-mipstar, ex-kac-quantum-bijection,
ex-kac-quantum-compiler, ex-free-unified-theory, ex-hs-masa-lift-positive, ex-hs-masa-lift-counter.

**Already reviewed elsewhere.**  No landing of these lanes carries a verdict in
`ex-review-groups-2026-09-12*` or `ex-review-analysis-2026-09-12*`.  Two structural checks
exist:
- the groups sweep (part 2 §2.0, to ~23:05 CDT) found no famous-root flip and no firing dead
  route for ex-complexity-sofic, ex-complexity-amenable and ex-free-unified-theory;
- the analysis baseline guard (§0.2, at `61a14d9b6`) covers the UGC, quantum PCP and
  non-hyperlinear-group roots before these lanes landed.

Neither re-derives any claim of these lanes, so nothing is skipped here.

For every node these lanes land as ESTABLISHED, and for every reduction others build on, the
argument is re-derived from the statement, and the statement and its citations are checked
against the sources (PDFs fetched on MSI and read page by page).  Verdicts:

- **PASS**: re-derived; the statement, every hypothesis and every citation match.
- **GAP**: the statement may be true, but the written argument does not prove it.  This covers a
  missing step, a hidden hypothesis, a citation clause that the source does not support, or a
  conditional stated as unconditional.  The owning lane is told what closes it.
- **FAIL**: the statement is false as written, or the argument has an error that no local fix
  repairs.  The node is corrected forward or its route retired, and the owning lane is told.

Priority:
1. anything that would decide a famous problem;
2. reductions others build on;
3. the rest.

The sweep criteria are those of the sibling reviews:
- a `requires: []` route whose invalidator is not itself established;
- prose saying "established" with no route into the claim;
- an id over 64 characters;
- a conditional result stated as unconditional.

## Verdict index

| § | claims | lane | verdict |
|---|---|---|---|
| 1 | `residual-finiteness-of-finite-presentations-is-pi2-complete`, `lef-of-finite-presentations-is-pi2-complete` and their five supporting nodes | complexity-sofic | **GAP, repaired and corrected forward (part 1).**  The theorem is true in my re-derivation.  The Lemma A input slip (`e_tau(c)`) was found by ex-verify-groups (part 3 §3.2) and fixed by the lane in `ec53d79731`.  **New here:** the import clauses "equal in `G(M)` iff equal in `S(M)`" and `T ≅ T_1` fail for zero elements under KMS v5's displayed relations G1--G8.  Lemma A Step 2 and Lemma B B4 use them, and ex-verify-groups §3.2 took them without re-reading.  Repair: the stop relations `x_(q_0 w) = 1`, as the new claim `kms-group-with-stop-relations-simulates-all-words` |

## Part files

- `research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md`: §1, residual finiteness and
  LEF of finite presentations (ex-complexity-sofic, landings 076f1bec8c and 0f7c32377c).
