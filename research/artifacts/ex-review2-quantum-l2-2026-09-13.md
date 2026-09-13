# EX review, second wave: quantum information, L²-invariants and complexity (2026-09-13)

Lane `ex-verify2-quantum-l2`, second-wave adversarial verifier of the EX swarm. Start tip `7d41d1a16a`.
Long sections go to part files `research/artifacts/ex-review2-quantum-l2-2026-09-13-part<N>.md`,
indexed at the end.

## 0. Scope and method

**Lanes.** ex-kac-quantum-bijection, ex-kac-quantum-compiler, ex-nh-mipstar, ex-ugc,
ex-ugc-rounding-pgroups, ex-quantum-pcp, ex-lueck-approximation, ex-atiyah-torsion-free,
ex-atiyah-base-change-td2, ex-determinant-monster, ex-kadison-kaplansky, ex-baum-connes,
ex-complexity-sofic.

**Census method.**
- **Nodes.** Every `research/<id>.md` path these lanes landed, per `state/landed.log` and
  `state/pushed-<lane>.tsv`, read at the tip: 284 paths, 153 claims, 4 retired. ex-atiyah-base-change-td2
  landed nothing under its own name; its transcendence-degree-one work landed as ex-atiyah-torsion-free
  (`d226d237e1`).
- **Established.** A fixpoint over the front matter of all 10,366 nodes at the tip. A route fires when
  every `requires` is established and no established claim `invalidates` it. The lower bound, which kills
  routes invalidated by the upper-bound set, and the upper bound, which kills only those invalidated by
  the lower-bound set, agree: 8,359 established claims. The count is local, not `cairn check`.
- **Reviewed.** An id counts as PASSED if it appears in backticks on a line containing `PASS` in any
  `research/artifacts/ex-review-*.md` or `review-*.md`. Every other mention of a census id was then read by
  hand.

**Famous roots of these lanes at the tip, all OPEN.** `unique-games-conjecture`,
`quantum-pcp-constant-gap-local-hamiltonian`, `determinant-conjecture`,
`determinant-conjecture-counterexample-exists`, `strong-atiyah-torsion-free`,
`kadison-kaplansky-torsion-free`, `kadison-kaplansky-counterexample-exists`,
`baum-connes-counterexample-group-exists`. No false establishment found.

**Verdicts.** The same as the sibling reviews:
- **PASS**: re-derived independently; the statement, hypotheses and citations match.
- **GAP**: may be true, but the written argument or its scope does not prove it as stated.
- **FAIL**: false as written, or broken beyond local repair.

## 1. Brief priorities already reviewed elsewhere, checked for freshness

Each row's verdict landed after the last change to the claim and its proof route. No node changed after
its review, so none is re-reviewed here.

| brief | claims | verdict, where | node last changed | review landed |
|---|---|---|---|---|
| (a) | `l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers` (Theorem D) | PASS after corrections, backlog part 1 §1.1 | 01:07 (the review's own correction) | 01:07 |
| (a) | `frame-acyclic-rings-have-low-degree-l2-acyclic-gl` (Theorem A), `binary-leavitt-unit-group-is-l2-acyclic` | PASS, backlog part 1 §1.2–1.3 | 09-12 22:10 | 01:07 |
| (b) | `determinant-conjecture-gives-one-variable-atiyah-base-change` | PASS (resultant plus Minkowski), groups part 10 §10.1 | 09-12 23:51 | 01:32 |
| (b) | `atiyah-base-change-in-transcendence-degree-one-under-det` | PASS, groups part 10 §10.2 | 00:07 | 01:32 |
| (c) | `free-subgroup-rounding-fails-for-non-normal-fibres` (`F_2 wr F_2^n`) | PASS, logic-quantum part 2 | 00:19 | 00:58 |
| (c) | `primitive-projective-representations-have-a-trace-gap` | PASS at node level, logic-quantum part 4; artifact read line by line here (part 1) | 00:31 | 01:22 |
| (d) | the five kac-quantum-bijection firewalls | PASS, logic-quantum parts 6–7 | 01:01–01:51 | 01:54–02:05 |
| (d) | `torsor-cfi-isomorphism-algebra-is-coset-constraint-algebra`, `torsor-cfi-port-profiles-are-cosets` | PASS, logic-quantum parts 4–5 | 00:54–00:56 | 01:22–01:47 |

The five firewalls:
- `independent-set-injection-splits-as-question-bijection`;
- `coset-systems-are-torsor-isomorphism-games`;
- `coset-refinement-forces-rectangular-central-splitting`;
- `exact-label-coset-refinements-are-affine`;
- `hidden-labels-import-cross-context-commutation`.

## 2. Census: established claims of these lanes with no PASS

The census has 33 claims. One is dropped after reading its mentions:
`integral-operator-norm-below-two-is-quantized` has a section-level PASS in groups part 2 §2.3. That
leaves 32.

**Derived claims (6):**

| claim | lane | route (requires) | prior mention |
|---|---|---|---|
| `kun-thom-wreath-is-not-rational-character-approximable` | determinant-monster | `-proof` (`hilbert-embeddable-witness-impossible`) | graph level only (groups part 2 §2.0). It kills the dead route `determinant-conjecture-via-rational-character-models` into a famous root |
| `determinant-conjecture-excludes-liouville-atiyah-exceptions` | atiyah-torsion-free | `liouville-atiyah-exceptions-proof` (`atiyah-base-change-holds-off-a-countable-set`) | "superseded, not re-derived" (groups part 10) |
| `purely-infinite-leavitt-path-v-monoid-cancellation` | lueck-approximation | `purely-infinite-leavitt-path-cancellation-agp-proof` (AGP import) | none |
| `kms-minsky-machine-groups-simulate-their-machines` | complexity-sofic | `-citation` | GAP, clauses 4–5 corrected forward (logic-quantum part 1 §1) |
| `residual-finiteness-of-enumerated-presentations-is-pi3-complete`, `residual-finiteness-two-generator-recursive-is-pi3-complete` | complexity-sofic | pre-EX Lean-backed proofs | listed as unreviewed (logic-quantum part 8 §8.2) |
| `arithmetical-complexity-table-of-group-properties` | complexity-sofic | ledger proof, many requires | famous cells only (logic-quantum part 8 §8.2) |

The six derived claims occupy five rows: the two Pi_3 completeness claims share one.

**Citation imports (26):**

| claim | lane | what feeds on it | prior source check |
|---|---|---|---|
| `binary-leavitt-frame-complexes-are-highly-acyclic` (Khanh Cor. 4.3) | lueck | `binary-leavitt-unit-group-is-l2-acyclic` | not re-read (backlog part 1 §1.3 re-derives only the frame-extension step) |
| `lueck-dimension-additivity-cofinality-and-induction` (Lück Thms 1.11, 1.18) | lueck | Theorem D | survey text quoted, backlog part 1 §1.1 |
| `l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup` (Lück Thm 6.4) | lueck | Theorem A | survey text quoted, backlog part 1 §1.1 |
| `agp-purely-infinite-simple-rings-have-cancellative-projectives` | lueck | path-algebra L² acyclicity | not re-read |
| `leavitt-path-algebras-purely-infinite-simple-criterion` (Abrams–Aranda Pino Thm 11) | lueck | path-algebra L² acyclicity | not re-read |
| `lamplighter-groups-have-irrational-l2-betti-numbers` (Grabowski) | lueck | irrational L²-Betti node | not re-read |
| `lamplighter-powers-have-undecidable-l2-kernel-and-zero-divisors` (Grabowski) | lueck | undecidable L² kernel node | not re-read |
| `gaboriau-commensurated-chain-fixed-price-criterion` (Gaboriau VI.24(3)) | lueck | Kun–Thom fixed price | not re-read |
| `integral-eigenvalues-galois-balanced-for-sofic-groups` (Thom Thm 1.1) | determinant-monster | `unbalanced-eigenvalue-certifies-nonsofic-support` | not re-read |
| `cyclotomic-integer-matrices-classified` (McKee–Smyth Thms 1–3) | determinant-monster | norm quantization | citation level, not the PDF (groups part 18 §18.5) |
| `smith-serre-measures-are-conjugate-limits` (Smith Thm 1.5) | determinant-monster | Serre-class nodes | citation level, not the PDF (groups part 18 §18.5) |
| `one-relator-groups-satisfy-strong-atiyah`, `strong-atiyah-passes-to-locally-indicable-extensions` (Jaikin-Zapirain–López-Álvarez Cor. 1.3, Prop. 6.5) | atiyah-torsion-free | Strong Atiyah reductions | citation level, not the PDF (groups part 18 §18.5) |
| `amenable-kernel-bc-transfer-and-ktop-half-exactness`, `bgw-trivial-coefficient-agreement-is-open` | baum-connes | module inexactness route | none |
| `lueck-surjective-assembly-traces-lie-in-lambda-g`, `zariski-dense-psl-subgroups-are-completely-selfless` | kadison-kaplansky | trace-image nodes | none |
| `commuting-hamiltonians-on-small-set-expanders-in-np`, `natarajan-vidick-games-pcp-amplification-error`, `nlts-hamiltonians-from-good-qldpc-codes`, `product-states-approximate-high-degree-2-local`, `two-local-degree-amplification-gives-np-witnesses` | quantum-pcp | qPCP attempts and stabilizer rounding | not re-read at source (logic-quantum part 8 §8.2) |
| `small-set-expansion-hypothesis-implies-ugc`, `affine-ug-easy-on-globally-hypercontractive-graphs`, `affine-ug-easy-on-certifiably-hypercontractive-graphs` | ugc | UGC reductions | not re-read at source (logic-quantum part 8 §8.2) |

Some rows cover two to five claims; the rows total 26.

**Order of work (brief item e).**
1. Imports whose failure would break a PASSED theorem: Khanh Cor. 4.3 and Thom Thm 1.1.
2. `kun-thom-wreath-is-not-rational-character-approximable`, which guards a famous root.
3. Theorem 16 of the ugc-rounding part 2 artifact, and the Theorem 12 steps it runs.
4. The remaining derived claims.
5. The remaining imports, from PDFs on MSI.

## 3. Verdict index

| part | items | verdict |
|---|---|---|
| 1 | Theorems 12, 14, 15 and 16, Proposition 13, Corollary 17 and Remark 18 of the ugc-rounding normal-fibre artifacts, read line by line | **PASS** |
| 1 | `kun-thom-wreath-is-not-rational-character-approximable` | **PASS at the checked steps**, conditional on the pre-EX `hilbert-embeddable-witness-impossible`. The original step 3 was correct: square roots of conditionally negative definite kernels are conditionally negative definite. This review's first "correction" was false and is retracted. Main now carries both arguments (`979f1c1def`) |
| 2 | eleven L², determinant and Strong Atiyah imports: Khanh, Thom, AGP, Abrams–Aranda Pino, Grabowski ×2, McKee–Smyth, Smith, Jaikin-Zapirain–López-Álvarez ×2, plus the Lück survey rows quoted in backlog part 1 | **PASS at source** |
| 2 | `purely-infinite-leavitt-path-v-monoid-cancellation`, `determinant-conjecture-excludes-liouville-atiyah-exceptions` | **PASS** (the second as a statement) |
| 3 | `amenable-kernel-bc-transfer-and-ktop-half-exactness`, `lueck-surjective-assembly-traces-lie-in-lambda-g`, `zariski-dense-psl-subgroups-are-completely-selfless`, `gaboriau-commensurated-chain-fixed-price-criterion` | **PASS at source** |
| 3 | `bgw-trivial-coefficient-agreement-is-open` (+ `-citation`) | **PASS at source after a notation FAIL.** Lemma A.1 of the erratum is about quotients onto `ℂ`; with an arbitrary quotient it would be false. Corrected forward in both nodes; no consumer misused it |
| 4 | five quantum-PCP imports (Aharonov–Eldar, Natarajan–Nirkhe, Anshu–Breuckmann–Nirkhe, Brandão–Harrow ×2) and three unique-games imports (RST, Bafna–Minzer, BBKSS) | **PASS at source** (SSEH ⇒ UGC through RST Cor. 3.3) |
| 4 | `port-generated-square-completions-force-coset-support`, `galois-games-round-linearly-for-bounded-fibre-size`, `abelian-normal-closure-fibres-round-linearly` | **PASS** (the first at artifact level; logic-quantum had all three at node level only) |
| 5 | wave-2 census: `forbidden-pair-splits-are-central-rectangle-splittings`, `fibre-commutative-quantum-isomorphisms-are-coset-systems` | **PASS** (MSSV Def. 2.7, Thm 3.1 and Lin Def. 3.15 checked at source) |
| 5 | `atiyah-base-change-in-transcendence-degree-two-under-det`, `atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set`, `determinant-conjecture-bounds-determinants-over-galois-orbits` | **PASS**, conditional as stated. Lemma H had a local GAP for rational points (`D = 1`); corrected forward in artifact part 2 |
| 6 | `kms-group-with-stop-relations-simulates-all-words`, logic-quantum's repair, checked independently | **PASS at the checked steps** (KMS v5 relations and Lemmas 4.9–4.14 read at source) |
| 7 | T2–T4 of `coset-systems-are-torsor-isomorphism-games` and EL2–EL3 of `exact-label-coset-refinements-are-affine` (node level only in logic-quantum) | **PASS** |
| 8 | the seven established Kac nodes (two from ex2-kac-forbidden-pair, five from ex-kac-quantum-bijection), all re-derived | **PASS** ×7; one justification in (H7) of the hidden-labels proof repaired forward |

## 4. Census tally (32 established, unpassed claims at the start)

- **PASS here: 26.**
  - Derived (3): the Kun–Thom obstruction, the Liouville exceptions, AGP cancellation.
  - Citation imports (23).
- **PASS by an earlier source quote: 2.** `lueck-dimension-additivity-cofinality-and-induction` and
  `l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup`. Backlog part 1 §1.1 quotes Lück's
  survey text at l. 334, 461 and 1880.
- **Reviewed elsewhere, GAP repaired: 1.** `kms-minsky-machine-groups-simulate-their-machines`
  (logic-quantum part 1 §1).
- **Not re-derived here: 3.** `residual-finiteness-of-enumerated-presentations-is-pi3-complete` and
  `residual-finiteness-two-generator-recursive-is-pi3-complete` are pre-EX, Lean-backed nodes that the
  lane only touched. `arithmetical-complexity-table-of-group-properties` is a ledger. Both were checked
  only for graph hygiene (4.1).
- **FAIL on a famous-problem claim: none. False establishment: none.**
- **4.1 Graph hygiene of the three unreviewed claims.**
  - **The two Pi_3 completeness nodes.** ex-complexity-sofic's only edit (`1343d6b78`) adds credit and
    framing. It cites Rauzy arXiv:2111.01190v2 and arXiv:2605.30138, and the KMS §1.1.7 question. It points
    to the Pi_2 proof of `residual-finiteness-of-finite-presentations-is-pi2-complete`, which logic-quantum
    part 1 passed after its repair. The statements are unchanged.
  - **The ledger.** It cites 30 claims: 26 compute established, and the other 4 are open.
    - `sofic-safe-finite-presentation-compiler` [S] is printed OPEN.
    - `amenability-of-finite-presentations-is-pi2-complete` [A] is printed OPEN.
    - `metabelianity-of-finite-presentations-is-recursively-enumerable` [MB] is printed "exact level OPEN".
    - `binary-leavitt-unit-group-hyperlinear` enters only the conditional cell [H] ("trivial or ...-hard")
      and a remark (l. 177).
    - No cell prints an open claim as settled.
- **Source items not re-read.**
  - Raghavendra–Steurer STOC 2010 Thm 1.4;
  - Bafna–Minzer Thms 1.6–1.8;
  - Panteleev–Kalachev and Leverrier–Zémor;
  - Natarajan–Nirkhe eq. (9);
  - the sentence in Ozawa §6 defining "completely C*-selfless";
  - the proof of BGW Lemma A.1.

## Part files

- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part1.md`: §1. Galois-game rounding at artifact
  level, and the Kun–Thom rational-character obstruction.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part2.md`: §2. The L², determinant and Strong
  Atiyah imports at source, and two derived claims.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part3.md`: §3. The Baum–Connes, Kadison–Kaplansky
  and fixed-price imports at source, and the BGW notation fix.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part4.md`: §4. The quantum-PCP and unique-games imports at source; port-generated completions and two Galois-game rounding claims.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part5.md`: §5. The wave-2 lanes ex2-kac-forbidden-pair and ex2-atiyah-base-change-td2, and the retraction note.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part6.md`: §6. The KMS group with stop relations.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part7.md`: §7. Coset-system quantum symmetry, exact-label affinity, and the Lück edit.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part8.md`: §8. Verdicts on the seven established Kac nodes.
