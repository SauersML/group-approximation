# EX review: backlog of finished EX lanes (2026-09-13)

Lane `ex-verify-backlog` (EX swarm), adversarial verifier. Start tip `98331ac9a`.

## 0. Scope and method

**Lanes.**
- ex-lueck-approximation, ex-hyperbolic-vtf, ex-weak-soficity.
- ex-free-bridges, ex-free-unused-power.
- ex-q34-leavitt-hs, ex-q34-kt-double, ex-q34-collapse, ex-nh-fresh.
- Refills, as they land.

**Skipped, already passed.**
- The Chern--Quillen chain of ex-hyperbolic-vtf (`ex-review-groups-2026-09-12-part2.md` §2.1).
- `leavitt-path-algebras-have-simultaneous-strong-division` (`review-backlog-2026-09-12.md` §14). It is
  consumed here as an input.

**Verdicts.**
- **PASS**: re-derived independently; the statement, hypotheses and citations match.
- **GAP**: the statement may be true, but the written argument, or its scope, does not prove it as stated.
- **FAIL**: the statement is false as written, or the argument is broken beyond local repair. A wording
  FAIL with a one-line fix is labelled as such and corrected forward.

**Citations.** Theorem numbers were checked against extracted text on MSI where that text exists, and each
item names the file. Otherwise the item says the import was not re-read. No computation was rerun for
parts 1--2.

## 1. Verdicts so far

| claim | lane | verdict | part |
|---|---|---|---|
| `l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers` (Theorem D) | lueck | PASS after a wording FAIL (empty `X`) and a scope GAP (countability), both corrected | 1 §1.1 |
| `frame-acyclic-rings-have-low-degree-l2-acyclic-gl` (Theorem A) | lueck | PASS | 1 §1.2 |
| `binary-leavitt-unit-group-is-l2-acyclic` | lueck | PASS | 1 §1.3 |
| `leavitt-tensor-host-unit-groups-are-l2-acyclic` | lueck | PASS | 1 §1.4 |
| `leavitt-unit-groups-over-every-field-are-l2-acyclic` | lueck | PASS | 1 §1.4 |
| `leavitt-path-unit-groups-with-trivial-unit-class-are-l2-acyclic` | lueck | PASS | 1 §1.4 |
| `binary-leavitt-unit-tracial-rank-functions-are-mixtures` | lueck | PASS | 1 §1.5 |
| `lamplighter-cube-embeds-in-binary-leavitt-unit-group` | lueck | PASS | 1 §1.5 |
| `binary-leavitt-unit-group-has-irrational-l2-betti-numbers` | lueck | PASS, wording note | 1 §1.5 |
| `decidable-groups-have-right-computable-l2-betti-numbers` | lueck | PASS | 1 §1.5 |
| `binary-leavitt-unit-group-has-undecidable-l2-kernel-problem` | lueck | PASS | 1 §1.5 |
| `kun-thom-wreath-is-l2-acyclic` | lueck | PASS | 1 §1.5 |
| `kun-thom-wreath-and-double-have-fixed-price-one` | lueck | PASS | 1 §1.5 |
| `kun-thom-double-has-vanishing-first-l2-betti-number` | lueck | PASS | 1 §1.5 |
| `simple-group-support-and-semisimple-rank-models-collapse` | weak-soficity | PASS, one justification repaired | 2 §2.1 |
| `simple-group-relator-width-in-finite-simple-targets` | weak-soficity | PASS, one exponent corrected | 2 §2.2 |
| `perfect-group-relator-width-over-nilpotent-groups` | weak-soficity | PASS | 2 §2.3 |
| `residually-finite-doubles-are-weakly-sofic` | weak-soficity | PASS, conditional on the Glebsky import | 2 §2.4 |
| `simple-vertex-groups-vtf-iff-some-finite-quotient` | hyperbolic-vtf | PASS, citation note | 2 §3.1 |
| `non-vtf-hyperbolic-counterexample-may-be-one-ended` | hyperbolic-vtf | PASS | 2 §3.2 |
| `lattice-forced-torsion-dies-in-hyperbolic-quotients`, with its dead route | hyperbolic-vtf | PASS | 2 §3.3 |
| triangle quotient search (artifact, and the open claim's Attempts) | hyperbolic-vtf | labelling PASS, support argument PASS, code not rerun | 2 §3.4 |

No FAIL on a claim that decides a famous problem. No false establishment found.

## 2. Forward corrections landed with parts 1--2

- **`l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers`.** "a countable group" becomes "a
  group", and "semisimplicial set" becomes "nonempty semisimplicial set".
- **`simple-group-relator-width-in-finite-simple-targets-proof`, §1.** `c q^rho` becomes
  `c q^(rk Q) >= c q`.
- **`simple-group-support-and-semisimple-rank-models-collapse-proof`, item 4.** The multiplicity bound for
  eigenvalues outside `F` now covers purely inseparable eigenvalues.

## 3. Sweep for false establishments (lanes of parts 1--2)

Method, bounded: I read the route and `requires` list of every claim reviewed. This is not a graph solve;
`ex-steward` runs `cairn check` on MSI.

**Established claims.** Every ESTABLISHED claim reviewed here has a route. Its `requires` name either
citation imports with `requires: []`, or established baseline claims. The conditional edges are named in
parts 1--2:
- `binary-leavitt-full-character-simplex`;
- `fpbs-elementary-matrix-semidirect-fixed-price-one`;
- `fpbs-amen2-betti-cost-input`;
- `kun-thom-nonsofic-wreath`;
- `kt-pair-group-double-is-nonsofic`;
- `kapovich-wise-rf-iff-finite-quotients`.

**Famous targets do not fire.**
- `non-weakly-sofic-group-exists`. Its route requires the open `fg-simple-weakly-sofic-groups-are-sofic`.
- `determinant-conjecture-counterexample-exists`. `determinant-counterexample-via-noncomputable-l2-betti-number`
  requires the open `decidable-group-with-noncomputable-l2-betti-number`, which has no route and carries
  Attempts.
- `non-virtually-torsion-free-hyperbolic-group` and `hyperbolic-group-without-finite-quotients`.
  `non-vtf-hyperbolic-via-simple-triangle-without-quotients` and `quotientless-hyperbolic-via-simple-triangle`
  require the open `hyperbolic-simple-triangle-group-without-finite-quotients`.
- `non-vtf-hyperbolic-via-lattice-forced-torsion-quotient` has `requires: []`, and an established
  invalidator kills it.

**Open claims without routes carry Attempts:** `kun-thom-double-is-l2-acyclic` and
`decidable-group-with-noncomputable-l2-betti-number`.

## 4. Queue

- ex-free-bridges: the three bridges. The re-derivation is done; part 3 is still to land.
- ex-free-unused-power: the hidden-solved claims.
- `howie-pro-p-tuple-fails-the-profinite-certificate-at-a5`.
- The ex-q34-* lanes and ex-nh-fresh.
- Refills, as they land.

## Part files

- `ex-review-backlog-2026-09-13-part1.md`: L²-acyclicity region (ex-lueck-approximation).
- `ex-review-backlog-2026-09-13-part2.md`: weak-soficity collapse and width (ex-weak-soficity), and VTF
  beyond Chern--Quillen (ex-hyperbolic-vtf).
