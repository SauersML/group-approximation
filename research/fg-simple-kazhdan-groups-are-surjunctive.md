---
rg: 2
id: fg-simple-kazhdan-groups-are-surjunctive
kind: claim
title: Every finitely generated simple Kazhdan group is surjunctive
distinct_from:
  finitely-generated-simple-groups-are-surjunctive: that asks it for every finitely generated simple group; this asks it only for the Kazhdan subclass. Both are equivalent to Gottschalk's conjecture, by Schupp's embedding for that one and by simple Kazhdan containers for this one.
  fixed-gottschalk-test-group-is-surjunctive: that asks it for one fixed finitely presented host that is neither simple nor Kazhdan-known; this asks it for the class of finitely generated simple Kazhdan groups.
  leavitt-unit-group-surjunctive: that asks it for one member of this class, the binary Leavitt unit group; this asks it for every member.
artifacts:
  - research/artifacts/simple-kazhdan-hosts-2026-09-12.md
---

**OPEN.** For every finitely generated infinite simple group `G` with property
(T) and every finite alphabet `A`, every injective cellular automaton
`A^G -> A^G` is surjective.

By `gottschalk-reduces-to-fg-simple-kazhdan-groups` this is equivalent to
Gottschalk's conjecture. So an attack may assume a simple Kazhdan host, and a
counterexample, if one exists, lives on one.

## Attempts

- **Permanence.** A host containing a finitely presented simple nonsofic
  FA group, such as `R^x`, lies outside every closure of the sofic groups under
  subgroups, colimits, extensions, graphs of groups and marked limits
  (`fixed-host-outside-sofic-permanence-closure`).
- **Counting.** Gromov--Weiss counting needs sofic models. On a simple nonsofic
  host every nontrivial element is sofic-invisible, so
  `sofic-radical-localizes-garden-of-eden-windows` constrains nothing.
- **Periodic points.** On an infinite simple group the finite orbits are the
  `|A|` constants (Section 3.1 of the artifact). Lawton's argument and every
  finite-quotient argument are empty.
- **Measure and spectral invariants.** A strict automaton is a measure
  conjugacy onto its image, so the Koopman representation, spectral gap, strong
  ergodicity, orbit equivalence, cocycle superrigidity and Rokhlin entropy all
  agree on `mu_A` and `tau_* mu_A` (Section 3.2).
  - The proved upper bound is `strict-automaton-lowers-bernoulli-rokhlin-entropy`.
  - What is missing is a lower bound on Bernoulli Rokhlin entropy (INF). No
    property (T) mechanism for one is known.
  - INF passes to subgroups (`bernoulli-rokhlin-maximality-passes-to-subgroups`),
    so INF for every group also reduces to this class. That reduction is the
    route `rokhlin-maximality-via-fg-simple-kazhdan-hosts`, into the hole
    `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`.
  - `sofic-radical-localizes-bernoulli-deficit-witnesses` folds every deficit
    witness on a sofic-invisible element. On a simple nonsofic host the sofic
    radical is the whole group, so this constrains only the subgroup a witness
    generates.
- **Bernoulli rigidity.** Dead. `compressed-coset-shifts-carry-strict-equivariant-embeddings`
  gives a simple Kazhdan group with a Bernoulli coset shift that has every
  Kazhdan and simplicity property of the full shift and still carries a strict
  continuous equivariant embedding. That kills
  `fg-simple-kazhdan-surjunctive-via-bernoulli-rigidity`. A proof must use
  freeness of the regular action, i.e. Curtis--Hedlund--Lyndon locality.
- **Operators.** Trace-level premises are zero-one
  (`injective-ca-product-trace-zero-one-law`). With translations and, under
  (T), all compact operators added, the range projection stays at distance
  `1/2` (`range-projection-far-from-translation-observables`).
- **Live targets:**
  - INF on this class;
  - locality over the free regular action forcing measure preservation
    (`injective-measure-preserving-ca-is-surjective`);
  - on the negative side, a strict automaton on some such host, for example
    `R^x` (`leavitt-unit-group-nonsurjunctive`).
- **Digest (gk-archive, 2026-09-12).** **Proved:**
  - both reductions (`countable-group-embeds-in-fg-simple-kazhdan-group`,
    `gottschalk-reduces-to-fg-simple-kazhdan-groups`) and the simple-host form
    `finitely-generated-simple-groups-are-surjunctive`;
  - subgroup heredity (`surjunctivity-passes-to-subgroups`);
  - the tower `V <= R^x <= A^x` (`leavitt-surjunctivity-tower`);
  - `R^x` is simple, FA and nonsofic (`leavitt-unit-group-is-simple-fa-nonsofic`), hence outside every
    permanence closure (`sofic-permanence-closure-omits-simple-fa-nonsofic-groups`,
    `leavitt-tower-outside-sofic-permanence-closure`);
  - the design filters that any counterexample must pass (`amenable-decoder-memory-forces-surjectivity`,
    `table-groups-are-memory-holonomy-groups`, `forward-relations-of-a-counterexample-have-a-nonsofic-core`,
    `strict-automata-live-on-canonical-table-groups`);
  - a certificate must live in one decidable host (`surjunctivity-recognition-dichotomy`).

  **Dead, beyond the entries above:**
  - Cantor coset peeling on `V` is circular (`thompson-v-coset-stabilizers-contain-copies-of-v`);
  - full-shift maps into infinite-stabilizer coset shifts are constant
    (`full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`);
  - (T) gives no rank-metric rounding over finite fields
    (`kazhdan-group-rank-models-admit-no-expander-decomposition`).

  **Live negative targets on hosts of this class:**
  - `ternary-anti-invariant-swap-corner-is-full` and `projective-ternary-klein-idempotent-is-full`,
    over `L_(F_3)(1,2)^x` and its scalar quotient;
  - the binary lifts over `R^x`;
  - `leavitt-units-have-zero-rokhlin-entropy-supremum` (measurable).

  **Live positive targets:** `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` and
  `every-injective-ca-preserves-uniform-bernoulli-measure`.
- **Untested ideas reported by lanes, not yet nodes (gk-archive, 2026-09-12).**
  - *gk-logic:*
    - **Boolean core.** For a fixed realizable forward and reverse table, does any alphabet admit
      strict rules? It looks like uniform network coding. Deciding it for small tables would either
      supply design candidates or exclude table shapes.
    - **Finite direct products.** It is open whether surjunctivity passes to them: the rectangle
      clauses are disjunctive, not Horn.
    - **Two-generator bridge.** Test whether the bridge in
      `second-level-rice-theorem-for-local-approximation-properties` works for surjunctivity. That is
      open cell 8 of `arithmetical-complexity-table-of-group-properties`.
  - *gk-defect-automaton:* does some known surjunctive nonsofic group contain a nonsofic Kazhdan
    subgroup? A yes would show that nonsofic Kazhdan cores by themselves force nothing on the
    negative side.
- **Superrigidity on extensions (gk-p-inf-kazhdan, 2026-09-12).** Artifact
  `research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md`.
  - Over every finitely generated infinite simple Kazhdan host, every ergodic finite-to-one
    extension of a Bernoulli action is an isomorphism
    (`kazhdan-map-bernoulli-finite-extensions-are-trivial`). So a strict design cannot use an
    invariant lift on which its decoder is finite-to-one.
  - Every strict pair, over any group, carries relatively weakly mixing positive-entropy lifts
    (`strict-pair-flip-lifts-are-relatively-weakly-mixing`). Superrigidity collapses only finite
    and compact parts, so it can never contradict a strict pair.
  - These hosts are minimally almost periodic
    (`fg-infinite-simple-groups-are-minimally-almost-periodic`).
