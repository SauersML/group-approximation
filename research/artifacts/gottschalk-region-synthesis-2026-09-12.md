# Gottschalk region synthesis after waves 3 and 4

Lane `w5-strategist-synth`, 2026-09-12, read at main tips d7f44c4644 through 30afe9e72c. Read-only synthesis
of the Cairn region around `gottschalk-surjunctivity-conjecture`, plus three wiring routes (Section 5). Nothing
here decides the goal or a landmark.

## 0. Conventions

- **E✓**: established, with a verifier verdict line on its proof route.
- **E**: established on main with no verdict line found on its proof route.
- **O**: open. **I**: imported literature.
- A chain is **one lemma from X** when every requirement on it except one is E✓, E or I.
- Fan-out counts are routes on main whose `requires` names the node (block and inline lists, tip 8660f5cebd).

## 1. Counterexample chains into the goal's `refuted_by`

The goal lists eight roots. `higman-group-nonsurjunctive` (933b7aa5e) is a ninth root and is not yet listed.

### C1. Ternary state-upgrade chain (the most decisive chain on main)

```text
goal  <-refuted_by-  ternary-leavitt-unit-group-nonsurjunctive (O)
  <- nonpositive-unit-class-refutes-ternary-surjunctivity
       [stable-finiteness-failure-refutes-surjunctivity (I)]
  <- ternary-anti-central-unit-class-is-nonpositive (O)
  <- ternary-counterexample-from-rank-kill-and-state-realization
       (K)  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one (O)
       (U1) ternary-anti-central-states-give-sylvester-rank-functions (O)
            anti-central-state-obstruction-equals-stable-finiteness (E✓, gk-vf-linear §11)
```

- **(K) via V.** `ternary-units-kill-minus-one-via-thompson-v-augmentation` needs:
  - `thompson-v-ternary-rank-functions-are-augmentation` (O);
  - `signed-thompson-z-moving-rank-functions-match-v-rank-functions` (E✓, w4-vf-gate §21.1).
  So (K) follows from the characteristic-three Sylvester gate of Thompson's V. That is stronger than (K), since
  it also makes V nonsofic.
- **(U1) via weakly finite images.** `sylvester-rank-functions-from-weakly-finite-images` needs:
  - `anti-central-rank-condition-gives-weakly-finite-image` (E, no verdict line on either proof route);
  - `anti-central-weakly-finite-images-carry-rank-functions` (O), step U1b.
- **(U1) via certificates.** `anti-central-triangular-certificates-flatten-to-minors` (O) gives (U1) with
  `sylvester-rank-functions-iff-no-triangular-certificate` (E✓, w4-vf-linear-b §28.1). This route is landed in
  this synthesis (Section 5). The general form `rank-condition-rings-carry-sylvester-rank-functions` (O) implies
  the flattening.
- **Audit.** w5-red-upg (d0dbabbff) re-derived links 3–6 and passed them. Links 1–2 are the two open lemmas.
- **Net.** The chain is **two lemmas from a counterexample**: every Sylvester rank function on F_3[V] is the
  augmentation rank (or just (K)), and U1b. U1b uses no group input beyond the structure of S_-.
- **Superseded parallel route.** `ternary-counterexample-from-rank-triviality-and-state-upgrade` requires the
  all-fields claim `leavitt-el3-rank-models-over-finite-fields-are-trivial` (all finite K, all n >= 2). Only
  K = F_3, n = 2 is used, and the rank-model form of (U1) (`ternary-anti-central-states-force-nontrivial-rank-models`)
  is now unnecessary by w3-gate-char3's abstract scope (1bace02f7).

### C2. Binary state-upgrade chain (w5-binary-upg)

```text
goal <- leavitt-unit-group-nonsurjunctive <- nonsurjunctive-from-stable-finiteness-failure [I]
  <- leavitt-group-algebra-not-stably-finite (O) <- stably-finite-failure-from-direct-finiteness-failure
  <- leavitt-unit-group-algebra-not-directly-finite (O, 15 incoming routes)
  <- binary-cyclic-corner-fullness-gives-kaplansky-failure
  <- binary-cyclic-averaging-idempotent-is-full-on-leavitt-units (O)
  <- binary-counterexample-from-rank-kill-and-state-realization
       sylvester-rank-functions-on-leavitt-units-kill-two-root-defect (O)     binary Sylvester gate
       binary-complement-corner-states-give-sylvester-rank-functions (O)     binary U1
       binary-complement-corner-rank-functions-pull-back-to-units (E, no verdict line)
```

**Net: two lemmas from a counterexample.** It is the same shape as C1: a Sylvester gate plus a state-to-rank-function
upgrade.

### C3. Ternary corner, one lemma

`anti-invariant-swap-corner-refutes-ternary-surjunctivity` needs `ternary-anti-invariant-swap-corner-is-full` (O,
fan-out 7), `ternary-leavitt-swap-problem-splits-at-central-involution` (E, no verdict line) and I.
- **Equivalences.** The corner is full iff the unit class is nonpositive (Theorem E). It is full iff
  `anti-central-lifted-trace-is-relatively-positive` fails (criterion E✓, w4-vf-linear-b §24; premise
  `anti-central-k0-states-equal-lifted-trace-on-signed-thompson` E✓ §12).
- **Kills.** Any Sylvester rank function moving z kills it (E✓). If V is sofic, no witness is supported in
  E⋊V (c4f44ada5).
- **Relation to C1.** C3 is the one-lemma form, and C1 splits that lemma into (K) and (U1).

### C4. Binary Kaplansky, one lemma per route

`leavitt-unit-group-algebra-not-directly-finite` has 15 incoming routes: visible lifts, invisible kernel pairs,
laminar finite-subgroup defects, idempotent equivalence, averaging corners, and others. Each is one lemma from C2's
root. Each lemma is at least as hard as `non-linear-sofic-group`, because linear soficity of R^x kills all of them
(`non-linear-sofic-via-leavitt-kaplansky-failure`).

### C5. Host roots, one lemma each (a stable-finiteness failure)

| root | open lemma | other requirements |
|---|---|---|
| `deligne-triple-cover-nonsurjunctive` | `deligne-twisted-group-algebra-is-not-stably-finite` | I |
| `kun-thom-clifford-cover-nonsurjunctive` | `clifford-cover-anti-half-skew-ring-not-directly-finite` | splitting E✓, I |
| `strict-automaton-on-lattice-in-product-of-trees` | `radu-bmw-lattice-nonsurjunctive` | Titz–Witzel I |
| `some-finite-field-leavitt-unit-group-nonsurjunctive` | `leavitt-visible-cyclic-corner-is-full-on-some-host` | three E/I |
| `projective-ternary-leavitt-group-nonsurjunctive` | `projective-ternary-swap-idempotent-is-full` | E/I |
| `kun-thom-wreath-lamp-quotient-nonsurjunctive` | none: no incoming route | — |
| `higman-group-nonsurjunctive` | none: no incoming route, not in the goal's `refuted_by` | — |

## 2. Landmark chains

`non-linear-sofic-group` has 13 incoming routes, and this synthesis adds two (Section 5).

| id | open lemma | other requirements | net |
|---|---|---|---|
| L1 SUB | `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` | defect gap E✓ (§8.1), near-minimal multiplicativity E✓ (§8.3) | one lemma |
| L1′ commutant | `some-commutant-element-distorts-defect-range-rank` | commutant faithfulness E (stronger independence E✓), defect gap E✓ | one lemma, implied by L1 |
| L2 Sylvester | `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect` | augmentation theorem E (w3-vf-linear, ecba807a0) | one lemma = gate, Sylvester form |
| L3 Cohn | `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`, fed by `binary-jacobson-el3-rank-radical-is-the-finitary-kernel` | matrix units, extraction, no unital rank model | one lemma; route landed here |
| L4 V (char 2) | `thompson-v-has-no-nontrivial-f2-rank-model` | — | one lemma |
| L4′ V (char 3) | `thompson-v-ternary-rank-functions-are-augmentation` | — | one lemma; route landed here |
| L5 restatements | level contraction, rank-four Cuntz family, covariant diagonal, ring rank approximability, EL_3 ring rigidity, rigid compression defects, projective swap, Deligne central mark (RGR_p + Sp_4 Schur certificate) | — | equivalent to or stronger than a gate |

**L1 firewalls (all E✓ by w4-vf-gate).** A proof of the SUB lemma cannot come from:
- finite-subgroup data: Weyl elements, halving sheets, prefix doubling, the swap, torus or compressor conjugations;
- multiple HNN extensions of a locally finite subgroup along single-letter conjugations (§20.1);
- the cylinder commutant at near-minimal defect;
- unitriangular regular models.

**What L1 must use instead.** Relations among two or more letters outside one locally finite subgroup and outside
the cylinder commutant. Examples:
- V's multiplication table on depth-changing letters;
- commutation of disjointly supported depth-changing letters;
- the Toeplitz commutator at compressors.

The Fock tower (`fock-local-letters-extend-level-models-with-disjoint-commutation`, E) realizes disjoint
commutation exactly. Its compressors miss the Toeplitz relation by exactly a quarter
(`natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter`, E), and that relation is where L1's lemma would live.
The regular-ring transfer (`leavitt-defect-descent-chain-holds-in-regular-rank-rings`, E✓ §18.3) means a
regular-ring proof of L1 excludes every regular homomorphism. With `sylvester-rank-functions-on-leavitt-units-are-regular`
(O, no route out) it would settle L2.

## 3. Positive chains into the goal

| route | open lemma | net |
|---|---|---|
| `gottschalk-via-uniform-single-site-output-law` | `every-injective-ca-has-uniform-single-site-output-law` | restatement (equivalent to the goal) |
| `gottschalk-via-maximal-bernoulli-rokhlin-entropy` | `bernoulli-rokhlin-entropy-maximal-for-every-group` (fan-out 7) | one lemma, a known hard problem |
| `gottschalk-via-fg-simple-kazhdan-hosts` | `fg-simple-kazhdan-groups-are-surjunctive` | restatement |
| `gottschalk-via-unbalanced-table-memory-collisions` | `unbalanced-forward-tables-identify-memory-letters` | restatement (Theorem 3 of its artifact) |
| `gottschalk-via-quotient-closure` | `surjunctivity-passes-to-quotients` | restatement |
| `stable-formalization-reduces-surjunctivity-to-kaplansky` | `injective-binary-automata-are-stably-formalizable` plus Kaplansky | two lemmas, 2^n alphabets only |
| `gottschalk-via-window-entropy-deficit`, `gottschalk-via-flip-lift-and-zero-fiber-entropy` | — | invalidated (inline `invalidates`) |

**Settled small cases.**
- `three-address-binary-injective-rules-are-balanced` (E✓, two proof routes).
- `single-patch-ternary-rules-reduce-to-linear-strictness` (E, pending w3-vf-nonlinear).
- `three-point-decoder-memory-injective-ca-are-surjective` (O) is not wired into any route.

## 4. Near-misses, ranked

Ranked by decisiveness, then by how specific the remaining lemma is (a technical lemma rather than a known
open problem restated).

1. **C1, two lemmas from a Gottschalk counterexample.**
   - **(K):** `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`. Every Sylvester matrix rank
     function on F_3[G_3] has rk(1 − [z]) = 0. The char-3 Sylvester gate of V implies it.
   - **U1b:** `anti-central-weakly-finite-images-carry-rank-functions`. A nonzero weakly finite quotient W of S_-,
     with all K_0 states faithful on idempotent matrices and G_3 embedded with z ↦ −1, carries a Sylvester
     matrix rank function. The certificate form is `anti-central-triangular-certificates-flatten-to-minors`.
   - **Why this ranks first:** U1b has no group input.
   - **Kill test:** a W with the rank condition but no rank function. Such a W needs a non-idempotent triangular
     step at a mixed minor (c1b9da39b).
2. **L3, one lemma from `non-linear-sofic-group`.** `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`,
   equivalently that EL_3(C_2) has no injective characteristic-two rank model (013740e0d). It is itself fed by
   `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`. The route out is landed here.
3. **L1, one lemma from the landmark, both premises verified.** The strict submultiplicativity deficit θ < 1.
   Section 2 lists what the lemma can no longer use. The live input is at least two letters outside one locally
   finite subgroup, the natural candidate being the Toeplitz quarter defect of Fock compressors.
4. **C3, one lemma from a counterexample.** The ternary swap corner. Equivalent forms:
   - the nonpositive unit class;
   - failure of lifted-trace relative positivity.
   It is the one-lemma form of C1.
5. **C2, two lemmas.** The binary Sylvester gate plus the binary state upgrade, as C1 with (K) replaced by
   rk(D) = 0.
6. **L4 and L4′, one lemma.** The Sylvester gates of V, in characteristic 2 and in characteristic 3. Either makes
   V nonsofic. L4′ also gives (K).
7. **C5, one lemma per host.** A stable-finiteness failure of one algebra. None of these has a candidate.
8. **Positive side.** Maximal Bernoulli Rokhlin entropy is one lemma from the goal, and a known hard problem.
   Every other positive route is a restatement.

No new open claim is needed for a near-miss. Each remaining lemma is already a node. The gaps were three missing
routes out of existing nodes, landed in Section 5.

## 5. Routes landed by this synthesis

- **`non-linear-sofic-via-cohn-el3-two-root-identity`.** Requires the Cohn claim, the reversed-root identity, the
  matrix-unit criterion, extraction, and no unital rank model. Target: `non-linear-sofic-group`.
- **`anti-central-rank-functions-from-certificate-flattening`.** Requires the flattening claim and the certificate
  criterion. Target: (U1).
- **`non-linear-sofic-via-thompson-v-ternary-augmentation`.** Requires the char-3 V gate. Target:
  `non-linear-sofic-group`.

## 6. Load-bearing nodes and roster coverage

The five open nodes whose resolution settles the most chains:

| node | settles | roster (RULES.md WAVE 4–5) | gap |
|---|---|---|---|
| `thompson-v-ternary-rank-functions-are-augmentation`, with binary twin `thompson-v-has-no-nontrivial-f2-rank-model` | C1 (K), V nonsofic, L4′; if false, the E⋊V corner witnesses die | w5-c3-signed-thompson (landed the equivalence), w5-v-infinite-order (binary) | No lane is named for the char-3 V gate itself. w4-gate-v2's torsion theorem covers odd p ≠ char only, so 3-cycles over F_3 are untreated. |
| `anti-central-weakly-finite-images-carry-rank-functions` (U1b), with the flattening claim | C1 (U1); with (K), a counterexample | w4-upg-state, w4-upg-kill, w5-red-upg; binary twin w5-binary-upg | covered |
| `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, with ternary twin `ternary-disjoint-cylinder-defects-strictly-submultiplicative` | L1, L1′, and L2 via regularity | w4-sub-*, w5-c3-submult, w5-c3-descent | See the three gaps below this table. |
| `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect` | L2, C2 | w4-tensor-rankfn, w5-binary-upg | `sylvester-rank-functions-on-leavitt-units-are-regular` has no route out and no named owner |
| `ternary-anti-invariant-swap-corner-is-full` (fan-out 7) | C3, and through Theorem E everything in C1 | implicit through C1 | none; attack it through C1's two lemmas |

**SUB gaps.**
- All three SUB lanes ended at firewalls.
- No lane is assigned to the one live input class: multi-letter relations such as V's multiplication table,
  disjoint commutation of depth-changing letters, or the Fock compressors' Toeplitz quarter.
- The ternary twin has no route out, and its descent premises (char-3 defect gap, near-minimal multiplicativity)
  are not on main.

**Positive-side gap.** `bernoulli-rokhlin-entropy-maximal-for-every-group` has fan-out 7 and no wave-4 or wave-5
lane since w3-inf-b finished.

## 7. Duplicates, contradictions and wiring defects

- **No two-sided established refutation.** At tip d7f44c4644, all 419 `refuted_by` pairs were checked against
  first body markers, and none has both ends ESTABLISHED.
- **Invalidated goal routes.** The goal's two INVALIDATED routes are window entropy deficit and flip lift, both
  invalidated inline. That matches the steward.
- **Roots without routes.** `kun-thom-wreath-lamp-quotient-nonsurjunctive` has no incoming route.
  `higman-group-nonsurjunctive` has none either, and is missing from the goal's `refuted_by`. That is the
  steward's edit.
- **Over-strong requirement.** `ternary-counterexample-from-rank-triviality-and-state-upgrade` requires the
  all-fields, all-n EL_3 triviality claim, where only (F_3, n = 2) is used. It is superseded by the
  Sylvester-form route, and its author could mark it so.
- **Duplicate names for the binary gate.** The same gate, or a sufficient form of it, has at least 15 names:
  - equivalent restatements: `rank-models-of-el3-satisfy-the-two-root-identities`, `leavitt-el3-rank-models-over-finite-fields-are-trivial`
    (binary instance), `leavitt-corner-deviations-vanish-along-levels`, `rank-four-isometry-relations-give-corner-cuntz-family`,
    `leavitt-two-root-defect-piece-forces-covariant-diagonal`, `leavitt-unit-linear-soficity-is-ring-rank-approximability`
    (collapsed), `el3-rank-models-factor-through-ring-rank-models` (class form), `f2-linear-sofic-groups-kill-rigid-compression-defects`;
  - negations: `binary-leavitt-unit-group-is-f2-linear-sofic`, `binary-leavitt-units-carry-nonaugmentation-rank-function`;
  - stronger forms: `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`;
  - sufficient forms: `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, `some-commutant-element-distorts-defect-range-rank`,
    `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`, `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`,
    `thompson-v-has-no-nontrivial-f2-rank-model`.
  - Consequences: 13 of the routes into `non-linear-sofic-group` are restatements of one open gate, so counting
    routes overstates progress. Treat them as one front.
- **Duplicate forms of (U1).** Five names:
  - `ternary-anti-central-states-force-nontrivial-rank-models` (rank-model form, superseded);
  - `ternary-anti-central-states-give-sylvester-rank-functions` (Sylvester form);
  - `anti-central-triangular-certificates-flatten-to-minors` (certificate form);
  - `anti-central-weakly-finite-images-carry-rank-functions` (U1b);
  - `rank-condition-rings-carry-sylvester-rank-functions` (general).
  All are now wired into (U1).
- **Established premises with no verdict line on their proof routes, in decisive chains:**
  - `anti-central-rank-condition-gives-weakly-finite-image` (C1, U1a);
  - `binary-complement-corner-rank-functions-pull-back-to-units` (C2);
  - `ternary-leavitt-swap-problem-splits-at-central-involution` (C3);
  - `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant` (L1′; its stronger twin is verified);
  - `binary-leavitt-unit-group-is-simple` (EL_3 ring rigidity route);
  - `leavitt-unit-group-carries-nontrivial-rigid-defect` (rigid compression route);
  - `strict-automata-live-on-canonical-table-groups` (unbalanced-table route);
  - `injective-ca-random-order-transport-identity` (random-order transport).
  None is known wrong. The first two sit in the counterexample chains and should be verified first.
- **Name drift.** Reports and lead messages cite `binary-three-address-injective-automata-have-balanced-rules`. Main
  has `three-address-binary-injective-rules-are-balanced`, with two independent proof routes from w3-bal-design
  and w4-bal-census, both verified.
