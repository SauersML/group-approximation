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
| 1 | `kun-thom-wreath-is-not-rational-character-approximable` | **PASS at the checked steps**, conditional on the pre-EX `hilbert-embeddable-witness-impossible`. Step 3's length convention was misstated; corrected forward in the route |
| 2 | eleven L², determinant and Strong Atiyah imports: Khanh, Thom, AGP, Abrams–Aranda Pino, Grabowski ×2, McKee–Smyth, Smith, Jaikin-Zapirain–López-Álvarez ×2, plus the Lück survey rows quoted in backlog part 1 | **PASS at source** |
| 2 | `purely-infinite-leavitt-path-v-monoid-cancellation`, `determinant-conjecture-excludes-liouville-atiyah-exceptions` | **PASS** (the second as a statement) |
| 3 | `amenable-kernel-bc-transfer-and-ktop-half-exactness`, `lueck-surjective-assembly-traces-lie-in-lambda-g`, `zariski-dense-psl-subgroups-are-completely-selfless`, `gaboriau-commensurated-chain-fixed-price-criterion` | **PASS at source** |
| 3 | `bgw-trivial-coefficient-agreement-is-open` (+ `-citation`) | **PASS at source after a notation FAIL.** Lemma A.1 of the erratum is about quotients onto `ℂ`; with an arbitrary quotient it would be false. Corrected forward in both nodes; no consumer misused it |

## Part files

- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part1.md`: §1. Galois-game rounding at artifact
  level, and the Kun–Thom rational-character obstruction.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part2.md`: §2. The L², determinant and Strong
  Atiyah imports at source, and two derived claims.
- `research/artifacts/ex-review2-quantum-l2-2026-09-13-part3.md`: §3. The Baum–Connes, Kadison–Kaplansky
  and fixed-price imports at source, and the BGW notation fix.
