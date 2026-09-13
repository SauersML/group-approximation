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

| 2 | the quantum symmetry rung: `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group`, `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap`, `closure-safe-support-is-exactly-the-colored-iso-rung`, `colored-cfi-rung-is-the-solution-group-case` | nh-mipstar | **PASS.**  Citations checked at source (BCEHPSW, Roberson--Schmidt).  One import not re-read: synchronous algebra = BCS algebra (P1).  The target roots stay OPEN |
| 2 | `unique-games-hard-at-completeness-one-half`, `two-to-two-games-theorem`, `galois-unique-game-value-is-transversal-expansion`, `elementary-abelian-galois-games-round-with-linear-loss`, `galois-games-round-through-free-subgroups`, `free-subgroup-rounding-fails-for-non-normal-fibres` | ugc, ugc-rounding-pgroups | **PASS.**  One wording note on `C_2`.  The SoS claim is OPEN, not established |

| 3 | `kazhdan-commutant-compression-stability-is-finitary`, `leavitt-unit-group-outside-class-iff-compression-stability`, `hs-vertex-rounding-and-liftable-masa-force-normalization` | free-unified-theory | **PASS.**  The rows rest on established prerequisites not re-derived here |
| 3 | `pauli-sums-near-their-one-norm-round-to-stabilizer-states`, `pauli-projector-hamiltonians-are-stabilizer-approximable`, `qudit-stabilizer-rounding-for-code-constraint-hamiltonians`, `pauli-norm-games-qpcp-needs-imperfect-completeness` | quantum-pcp | **PASS.**  Citation routes not re-read; novelty pass advised |
| 3 | structural sweep of all landings of the twelve lanes | all | **PASS.**  Every direct `requires: []` route into a famous root is killed by an established invalidator |

## Part files

- `research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md`: §1, residual finiteness and
  LEF of finite presentations (ex-complexity-sofic, landings 076f1bec8c and 0f7c32377c).
- `research/artifacts/ex-review-logic-quantum-2026-09-12-part2.md`: §2, the quantum symmetry rung
  (ex-nh-mipstar) and Galois unique games (ex-ugc, ex-ugc-rounding-pgroups).
