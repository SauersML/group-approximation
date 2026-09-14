---
rg: 2
id: v-self-similar-rewrites-preserve-strict-pairs
kind: claim
title: Self-similar rewrites of a rule pair over Thompson's V keep its tables and its strictness
invalidates: [thompson-v-surjunctive-via-self-similar-descent]
distinct_from:
  strict-automata-live-on-canonical-table-groups: that proves strictness of a rule pair depends only on its canonical table groups, over every group; this applies that to the isomorphisms V -> V_U and to products over disjoint clopens, and records that these rewrites change no invariant of the pair.
  thompson-v-coset-stabilizers-contain-copies-of-v: that shows the stabilizer families of the Cantor action contain copies of V, which kills coset peeling; this concerns rewriting the automaton itself through those copies, which leaves every table unchanged.
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**ESTABLISHED** by `v-self-similar-rewrites-preserve-strict-pairs-proof`.

Let `(tau, sigma)` be a left-inverse rule pair over `V`, with encoder memory `M`, decoder memory
`S` and rules `mu`, `nu`. Let `U` be a nonempty clopen and `phi : V -> V_U` an isomorphism.

1. The pair `(tau^phi, sigma^phi)` over `V`, with memories `phi(M)`, `phi(S)` and the same
   rules, has the same forward table (the partition of `S x M` by equal products) and the same
   reverse table. It is injective, surjective or strict exactly when `(tau, sigma)` is.
2. Let `(tau_i, sigma_i)`, `i = 1, 2`, have memories inside `V_(U_1)` and `V_(U_2)` for
   disjoint clopens `U_1`, `U_2`. Their product pair over the alphabet `A_1 x A_2` is a
   left-inverse pair, and it is strict exactly when at least one factor is strict.

So rewriting through `V_U ~= V` or through disjoint-support products changes none of the
following: the rules, the tables, the canonical table groups, the minimal reverse hinges, or
strictness. An induction on the automaton built from these rewrites has nothing that decreases.
