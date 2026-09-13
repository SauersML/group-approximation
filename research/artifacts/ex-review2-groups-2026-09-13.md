# EX review, wave 2: groups, geometry and logic (2026-09-13)

Lane `ex-verify2-groups` (EX swarm), adversarial verifier, wave 2. Start tip `7d41d1a16`.
This file is the index and census. Verdicts are written into part files as they land.

## 0. Scope and method

**Lanes (23).** ex-weak-sofic-classical-covering, ex-weak-sofic-deep-wreath, ex-fp-kazhdan-titz-witzel,
ex-fp-kazhdan-kac-moody, ex-fp-kazhdan-ring, ex-fp-simple-relation-climbing, ex-fp-simple-full-group-obstruct,
ex-hyperbolic-triangle-theory, ex-hyperbolic-triangle-search, ex-complexity-sofic-amplifier, ex-complexity-amenable,
ex-q34-unit-depth, ex-nonore-relative-gate, ex-nh-dyadic-pair, ex-q34-kt-wreath-soft-kernel, ex-q34-leavitt-hs,
ex-q34-kt-double, ex-q34-collapse, ex-left-orderable-nonsofic, ex-thompson-v-soficity, ex-free-bridges,
ex-free-unused-power, ex-free-objects.

**Census rule.**
- Collected every `research/<id>.md` these lanes landed, from the swarm's landing log: 390 paths, 200 claims and
  190 routes.
- Kept the claims whose body carries the ESTABLISHED marker: 108.
- Dropped every id that has a PASS heading, bold item or table row in `research/artifacts/ex-review-*.md` or
  `pc-lean-review-*.md` on main: 81 of the 108.
- That leaves 27: 26 marked ESTABLISHED, and one route-established claim with no status line.
- Re-added, at the brief's request, the lemmas that earlier passes explicitly did not re-derive (§1.1, §1.2).

**Verdicts.**
- **PASS**: re-derived independently; the statement, hypotheses and citations match.
- **GAP**: the statement may be true, but the written argument or its scope does not prove it as stated.
- **FAIL**: the statement is false as written, or the argument is broken beyond local repair.

**Computation.** Only the triangle certificates of §1.3 are rerun, once, on MSI, as a short job. A negative search
is never recorded as a theorem.

## 1. Census

### 1.1 Priority (a): ex-q34-kt-wreath-soft-kernel

| claim | earlier review | still to check |
|---|---|---|
| `kt-wreath-monomial-models-kill-fibre-even-lamps` | groups part 14 §14.3: PASS at the combining step; part 16 §16.5: step level | transport lemma (part 2 Theorem M); deep congruence (part 1 Lemma 2, part 2 Lemma 6, via Suslin); bounded-block extension (part 3 Lemma 10, Theorem M_k, Theorem 9) |
| `soft-kazhdan-central-elements-fixed-by-normal-closure` | none as a claim | all |
| `kt-clifford-cover-block-models-kill-the-sign` | none | all: part 4 identity (SC), Lemma 13, Theorem 12 |

### 1.2 Priority (b): ex-weak-sofic-classical-covering

| claim | earlier review | still to check |
|---|---|---|
| `simple-group-classical-width-finite-field-linear-soficity` | backlog part 7 §27.1: PASS at the checked steps | part 1 Lemmas 2.1, 3.1, 3.2 (independent re-derivation); part 2 Lemma 4.2 counts, Lemma 5.3 |
| `non-linear-sofic-simple-groups-bounded-width-in-classical-groups` | none | all, through `classical-width-from-finite-field-linear-sofic-dichotomy` |

### 1.3 Priority (c): ex-hyperbolic-triangle-search

| claim | earlier review | still to check |
|---|---|---|
| `a7a7a8-triangle-candidates-no-small-linear-representation` | backlog part 6 §17: PASS on method, certificates not rerun | one short MSI rerun of the certificates |
| `a7a7a8-triangle-candidates-no-4dim-char2-representation` | same | the sign identity for `G_2`, `G_4`; the rerun |

### 1.4 Priority (d): everything else in the census

| lane | claim |
|---|---|
| thompson-v-soficity | `almost-commuting-permutations-are-near-commuting` |
| thompson-v-soficity | `thompson-f-character-simplex` |
| thompson-v-soficity | `thompson-f-hyperlinear-iff-relator-system-hs-unstable` |
| thompson-v-soficity | `thompson-f-sofic-iff-relator-system-unstable` |
| free-objects | `bleak-quick-finite-presentations-of-thompson-v` |
| free-objects | `explicit-eighteen-relator-nonsofic-group` |
| free-objects | `explicit-sixty-relator-nonsofic-group` |
| free-objects | `leavitt-unit-group-finitely-presented` |
| free-objects | `leavitt-unit-group-steinberg-weyl-presentation` |
| free-objects | `leavitt-units-two-generator-fifteen-relator-presentation` |
| free-objects | `thompson-steinberg-presentation-of-leavitt-unit-group` |
| free-objects | `thompson-steinberg-three-generator-presentation` |
| q34-collapse | `hyperlinear-groups-closed-under-free-products` |
| q34-leavitt-hs | `leavitt-algebras-l-k-1-n-are-simple` |
| q34-leavitt-hs | `thompson-v-cyclic-subgroups-are-undistorted` |
| q34-leavitt-hs | `thompson-v-powers-have-linearly-growing-slope` |
| fp-simple-full-group-obstruct | `li-derived-full-group-homology-is-k-theory-cover` |
| weak-sofic-deep-wreath | `lucchini-menegazzo-unique-minimal-normal-generation` |
| weak-sofic-deep-wreath | `nikolov-segal-uniform-commutator-width` |
| left-orderable-nonsofic | `non-rf-hyperbolic-group-or-unique-product-nonsofic-group` |
| left-orderable-nonsofic | `relatively-kazhdan-amenable-pairs-allow-sofic-defects` |
| left-orderable-nonsofic | `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` |
| fp-kazhdan-titz-witzel | `ollivier-wise-kazhdan-rips-construction` |
| complexity-amenable | `arithmetical-complexity-table-of-group-properties` (no status line; route-established) |

Several (d) items are literature imports. For those, the check is the theorem number against the source.

**Coordination.** This census was sent to `ex-verify-groups` and `ex-verify-backlog` at landing. An item either of
them has already started is left to them and marked here.

## 2. Verdicts

No FAIL. No GAP. No false establishment found. Nothing reviewed here decides a famous problem.

| claim | verdict | part |
|---|---|---|
| `kt-wreath-monomial-models-kill-fibre-even-lamps` | PASS on the lemmas §14.3 left open (Lemmas 2, 6, 10; Theorems M, 7, M_k, 9) | 1 §§1--3 |
| `soft-kazhdan-central-elements-fixed-by-normal-closure` | PASS, one notation note (Lemma 10 cocycle display) | 1 §§2--3 |
| `kt-clifford-cover-block-models-kill-the-sign` | PASS | 1 §4 |
| `simple-group-classical-width-finite-field-linear-soficity` | PASS on part 1 Lemmas 1.4, 2.1, 3.1, 3.2 and part 2 Lemmas 4.1, 4.2, 5.3 | 2 §§1--5 |
| `non-linear-sofic-simple-groups-bounded-width-in-classical-groups` | PASS as an assembly, one notation note | 2 §6 |
| `a7a7a8-triangle-candidates-no-4dim-char2-representation` | PASS; certificates rerun on MSI and matched | 3 |
| `a7a7a8-triangle-candidates-no-small-linear-representation` | PASS at the checked steps; certificates rerun and matched | 3 |
| twelve literature imports (§1.4 list) | PASS, checked against the PDFs; citation notes on `li-derived-full-group-homology-is-k-theory-cover` and `ollivier-wise-kazhdan-rips-construction` | 4 §1 |
| `thompson-f-sofic-iff-relator-system-unstable`, `thompson-f-hyperlinear-iff-relator-system-hs-unstable` | PASS | 4 §2 |
| `relatively-kazhdan-amenable-pairs-allow-sofic-defects`, `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` | PASS | 4 §3 |
| `non-rf-hyperbolic-group-or-unique-product-nonsofic-group` | PASS as a dichotomy, justification note (Strojnowski); two imports unreviewed | 4 §3 |
| `thompson-steinberg-three-generator-presentation`, `leavitt-units-two-generator-fifteen-relator-presentation` | PASS | 4 §4 |
| `arithmetical-complexity-table-of-group-properties` | PASS at the ledger level | 4 §5 |

**Census corrections (part 4 §0).** Four ids were already PASSed in `ex-review-presentations-2026-09-12.md` §0 and
are dropped: `explicit-eighteen-relator-nonsofic-group`, `explicit-sixty-relator-nonsofic-group`,
`leavitt-unit-group-steinberg-weyl-presentation` and `thompson-steinberg-presentation-of-leavitt-unit-group`.

**Graph changes.** Review-status lines were landed on the seven (a)--(c) nodes (07d4db0cb8). Notes were sent to the
owner lanes: kt-wreath-soft-kernel, fp-simple-full-group-obstruct, fp-kazhdan-titz-witzel, left-orderable-nonsofic
and weak-sofic-classical-covering.

**Still unreviewed, found on the way.** `hyperbolic-kazhdan-cover-of-leavitt-unit-group` and
`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup` (consumed by the dichotomy), and
`chordal-abelian-graph-products-hs-stable` (consumed by the Thompson F HS equivalence): I found no PASS for them in the
review artifacts. The LEF finite-presentation node carries a stale "(unreviewed)" marker, though it was PASSed.

## 3. Parts

- `ex-review2-groups-2026-09-13-part1.md`: priority (a), the Kun--Thom wreath soft kernel.
- `ex-review2-groups-2026-09-13-part2.md`: priority (b), classical covering.
- `ex-review2-groups-2026-09-13-part3.md`: priority (c), triangle certificates rerun.
- Later parts: priority (d).
