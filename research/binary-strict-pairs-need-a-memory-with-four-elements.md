---
rg: 2
id: binary-strict-pairs-need-a-memory-with-four-elements
kind: claim
title: Over two symbols, a strict automaton pair realized in a group has a memory with at least four elements
distinct_from:
  three-address-binary-injective-rules-are-balanced: that shows injective two-symbol automata with at most three memory elements have balanced rules, whatever the decoder; this excludes strictness outright, but only when the decoder memory also has at most three elements.
  amenable-decoder-memory-forces-surjectivity: that excludes decoder memories generating amenable groups, among them every decoder memory of size two; this excludes size-three decoder memories over any encoder memory of size at most three, including those generating free groups.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that turns strictness into realized rectangle data and records the size-two exclusion; this decides every realized forward table of shape at most three by three over two symbols.
artifacts:
  - research/artifacts/gottschalk-small-memory-census-2026-09-13.md
---

**ESTABLISHED** by `binary-strict-pair-small-memory-census-proof`.

Let `G` be a group and `tau, sigma: {0,1}^G -> {0,1}^G` cellular automata with memories `M` and
`S`, both containing `1`, such that `sigma tau = id`. If `|M| <= 3` and `|S| <= 3`, then `tau` is
surjective.

Equivalently, no strict rectangle data with forward labels of sizes at most three, over two
symbols, is realized in any group. A counterexample to Gottschalk's conjecture over two symbols
needs an encoder or a decoder memory with at least four elements.

**What is new.** Memory sizes one and two were already excluded.
- A decoder memory of size two generates an amenable group
  (`amenable-decoder-memory-forces-surjectivity`).
- An encoder memory of size two generates a cyclic group. That group is residually finite, and the
  automaton is surjective iff its restriction to that subgroup is.

The new case is `|M| = |S| = 3`, where both memory groups can be free.

**Computer assisted.** The proof is an exact census on MSI (job 751675).
- Every word-problem decision is exact Tietze arithmetic or a replayed certificate.
- Two independent implementations test the rules.
- The scripts, the job log and the outputs are in
  `research/artifacts/gottschalk-small-memory-census-2026-09-13/`.

No verifier lane has re-derived the census.
