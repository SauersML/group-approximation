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
| `leavitt-unit-groups-have-fixed-price-one` | free-bridges | PASS | 3 §4.1 |
| `uniqueness-phase-cluster-relations-inherit-nonsoficity` and `nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu` | free-bridges | PASS; the Benjamini--Schramm route correctly does not fire | 3 §4.2 |
| `nonsofic-actions-have-cluster-soficity-threshold-in-pc-pu` and `nonsofic-subgroup-bounds-cluster-soficity-threshold` | free-bridges | PASS | 3 §4.3 |
| `sofic-coset-action-makes-amalgam-double-sofic` | hidden-solved | PASS | 3 §5.1 |
| `free-group-doubles-over-any-subgroup-are-sofic` and `gkp-free-group-actions-are-sofic` | unused-power | PASS | 3 §5.2 |
| `one-kun-thom-compressor-is-relatively-embeddable` | hidden-solved | PASS | 3 §5.3 |
| `commuting-kun-thom-compressors-are-relatively-embeddable` and `heisenberg-kun-thom-slice-is-relatively-embeddable` | hidden-solved | PASS at the checked steps | 3 §5.4 |
| `opposite-transvections-are-first-nonore-relative-gate` | hidden-solved | PASS | 3 §5.5 |
| the Farey, one-relator, two-coordinate, three-symbol and torsion-corner K2 claims | hidden-solved | PASS | 3 §5.6 |
| `rank-five-laurent-k2-stability-is-dimension-free` | hidden-solved | PASS, justification note on centrality | 3 §5.6 |
| `sofic-linear-weakly-sofic-chain-has-a-strict-link` | unused-power | PASS | 3 §5.7 |
| `howie-pro-p-tuple-fails-the-profinite-certificate-at-a5` | weak-soficity | PASS | 3 §6 |
| `thompson-elements-are-undistorted-in-leavitt-unit-group` | q34-leavitt-hs | PASS | 4 §7.1 |
| `thompson-v-has-no-heisenberg-subgroup`, with its three imports | q34-leavitt-hs | PASS | 4 §7.2 |
| `leavitt-unit-groups-over-finite-fields-mutually-embed` | q34-leavitt-hs | PASS | 4 §7.3 |
| `leavitt-north-south-thompson-unit-has-cyclic-centralizer` | q34-leavitt-hs | PASS | 4 §7.4 |
| `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex` | q34-kt-double | PASS as an implication | 4 §8.1 |
| `fournier-facio-vertex-rounding-fails-at-every-model` | q34-kt-double | PASS | 4 §8.2 |
| `kt-sofic-monomial-commutant-core-is-normalized` | q34-kt-double | PASS | 4 §8.3 |
| `block-monomial-hs-models-sofic-mod-amenable-soft-kernel` | q34-collapse | PASS | 4 §9.1 |
| `leavitt-units-admit-no-bounded-block-monomial-hs-model` and `kt-double-admits-no-bounded-block-monomial-hs-model` | q34-collapse | PASS | 4 §9.2 |
| `coarse-frame-normalizers-are-near-block-monomial` | q34-collapse | PASS | 4 §9.3 |
| `standard-identity-witnesses-force-block-displacement` and `leavitt-unit-microstates-are-asymptotically-primitive` | q34-collapse | PASS | 4 §9.4 |
| `monomial-rank-models-are-sofic-over-every-field` | q34-collapse | PASS at the outline level | 4 §9.5 |
| `period-doubling-subshift-algebra-is-its-own-matrix-ring` | nh-fresh | PASS | 4 §10.1 |
| `rf-kazhdan-group-not-flexibly-hs-stable` | hs-instability-kazhdan | PASS | 5 §11.1 |
| `finite-multiplier-projective-models-round-strictly` | hs-instability-kazhdan | PASS | 5 §11.3 |
| `one-compressor-actor-models-with-exact-origin-vertex` | hs-instability-extension | PASS at the checked steps | 5 §12 |
| `relator-width-over-nilpotent-by-locally-finite-groups` | weak-sofic-deep-wreath | PASS | 5 §13 |
| `simple-group-psl-width-is-finite-field-linear-soficity` | weak-sofic-classical-covering | PASS | 5 §14 |
| `simple-vertex-triangles-are-universal-for-triangle-vtf` | hyperbolic-triangle-theory | PASS | 5 §15 |

No FAIL on a claim that decides a famous problem. No false establishment found.

## 2. Forward corrections landed with parts 1--2

- **`l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers`.** "a countable group" becomes "a
  group", and "semisimplicial set" becomes "nonempty semisimplicial set".
- **`simple-group-relator-width-in-finite-simple-targets-proof`, §1.** `c q^rho` becomes
  `c q^(rk Q) >= c q`.
- **`simple-group-support-and-semisimple-rank-models-collapse-proof`, item 4.** The multiplicity bound for
  eigenvalues outside `F` now covers purely inseparable eigenvalues.
- **`a1-invariance-removes-polynomial-dimension-proof`** (landed with part 4). The centrality of
  `K2(r, R_d)` is now attributed to van der Kallen's theorem for commutative rings, rather than inferred from
  stabilization. (RFL4) is derived from normality and generation by the three symbols.

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

**Refill landings, first sweep at 01:07.** No refill route fires into a famous root.
- `non-vtf-hyperbolic-from-non-vtf-triangle` requires the open
  `hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free`.
- `no-heisenberg-from-linear-depth-growth` requires the open
  `leavitt-units-of-infinite-order-have-linear-depth-growth`.
- The two triangle routes between the non-VTF triangle claim and the simple-triangle claim form a 2-cycle,
  and both endpoints are open.

**Refill landings 01:09--01:44, second sweep at tip `b3083ac22`.** No route fires into a famous root.
- **`non-hyperlinear-group`.**
  - `non-hyperlinear-from-function-field-hecke-non-re` requires the open, routeless
    `function-field-hecke-pair-is-not-relatively-embeddable`.
  - `non-hyperlinear-from-opposite-slice-non-re` requires the open
    `opposite-transvection-slice-is-not-relatively-embeddable`. That claim's only route needs the same open
    Hecke claim.
- **The a7a7a8 triangle.** `a7a7a8-triangle-candidate-without-finite-quotients-instance` requires the open
  candidate claim.
- **No integer Heisenberg subgroup.** The two routes into `leavitt-unit-group-has-no-integer-heisenberg-subgroup`
  require the open `leavitt-units-of-infinite-order-have-linear-depth-growth` and
  `leavitt-unit-centralizers-have-finite-rank`.
- **Vertex instability.** `el-r-polynomial-vertex-not-flexibly-hs-stable` is OPEN. Its route requires the open
  `sl3-polynomial-covers-have-extra-finite-quotients`.
- **Centralizer normalization.** `kt-centralizer-normalization-hs` stays OPEN, as part 4 §8.4 records.
- **No status stated in prose.** The claims `a7a7a8-triangle-candidates-no-small-linear-representation` and
  `a7a7a8-triangle-candidates-no-4dim-char2-representation` have `requires: []` routes, so they compute
  established. They are first in the queue: the check is whether the exclusions are exhaustive proofs rather
  than search results.

## 4. Queue

- The two a7a7a8 representation exclusions.
- Refill claims established since 01:09:
  - `actor-extension-lifts-vertex-rounding-to-the-laurent-vertex`;
  - `unit-type-vertex-rounding-agrees-with-sigma-on-laurent-steinberg`;
  - `compressor-extension-makes-roundable-vertex-part-invariant`;
  - `one-compressor-wreath-has-models-with-exact-origin-vertex`;
  - `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`;
  - `deligne-symplectic-covers-are-not-schatten-approximated`, with its three citations;
  - `finite-simple-spectrum-gives-quotientless-hyperbolic-group`;
  - `convergent-quotient-count-decides-gromov-question`;
  - `linear-quotient-exclusion-lifts-from-char-zero`;
  - `leavitt-free-group-leading-term-forces-linear-depth`;
  - `leavitt-triangular-units-have-linear-depth-growth`;
  - `leavitt-heisenberg-centers-have-infinite-centralizer-rank`;
  - `simple-group-classical-width-finite-field-linear-soficity`;
  - `simple-group-width-over-all-finite-simple-groups`;
  - `non-linear-sofic-simple-groups-bounded-width-in-classical-groups`;
  - `simple-nonsofic-width-over-bounded-base-symmetric-wreath`;
  - `opposite-slice-contains-function-field-hecke-pair`;
  - `kt-double-hyperlinearity-requires-function-field-hecke-re`.

## Part files

- `ex-review-backlog-2026-09-13-part1.md`: L²-acyclicity region (ex-lueck-approximation).
- `ex-review-backlog-2026-09-13-part2.md`: weak-soficity collapse and width (ex-weak-soficity), and VTF
  beyond Chern--Quillen (ex-hyperbolic-vtf).
- `ex-review-backlog-2026-09-13-part3.md`: percolation bridges (ex-free-bridges); hidden-solved imports and
  the K2 chain (ex-free-unused-power); Howie's tuple.
- `ex-review-backlog-2026-09-13-part4.md`: the Q3.4 lanes (ex-q34-leavitt-hs, ex-q34-kt-double,
  ex-q34-collapse) and ex-nh-fresh.
- `ex-review-backlog-2026-09-13-part5.md`: refills, first batch (RF Kazhdan HS instability, finite
  multipliers, one-compressor models, nilpotent-by-locally-finite width, PSL width, triangle universality).
