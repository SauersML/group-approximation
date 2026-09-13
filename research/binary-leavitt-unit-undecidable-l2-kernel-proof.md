---
rg: 2
id: binary-leavitt-unit-undecidable-l2-kernel-proof
kind: route
title: Reduce Grabowski's lamplighter problems to the unit group through the lamplighter powers inside V
target: binary-leavitt-unit-group-has-undecidable-l2-kernel-problem
requires: [lamplighter-cube-embeds-in-binary-leavitt-unit-group, lamplighter-powers-have-undecidable-l2-kernel-and-zero-divisors, lueck-dimension-additivity-cofinality-and-induction]
---

**Embeddings.** `lamplighter-cube-embeds-in-leavitt-units-proof` builds `Z/2 ≀ Z` inside `V`,
supported in a cylinder. Its conjugates into the four disjoint cylinders `[00], [01], [10], [11]`
commute and give `H_4 = (Z/2 ≀ Z)^4 <= V <= G`. Three of them give `H_3 = (Z/2 ≀ Z)^3`. The
generators of `H_j` are fixed elements of `G`, so rewriting a matrix over `Z[H_j]` as a matrix over
`Z[G]` is a computable reduction.

**(1)** For `M` over `Z[H_3]`, induction is exact and preserves dimension, so
`dim_(N(G)) ker M = dim_(N(H_3)) ker M`. A closed invariant subspace has dimension zero iff it is
`{0}`. So `ker M = {0}` over `ℓ²(G)^k` iff over `ℓ²(H_3)^k`. A decision procedure over `G` would
decide Kernel-over-`Z[H_3]`, contradicting Grabowski's Theorem 2.

**(2)** Pick right coset representatives `G = ⊔ H_4 g_i`. Then `Z[G] = ⊕_i Z[H_4] g_i` as left
`Z[H_4]`-modules, and the same holds for matrices.
- If `M` over `Z[H_4]` satisfies `M Y = 0` with `Y` over `Z[G]`, write `Y = Σ Y_i g_i` with `Y_i`
  over `Z[H_4]`. Then `M Y_i = 0` for every `i`.
- If `Y != 0`, some `Y_i != 0`. The left-sided case uses left cosets.
- So `M` is a zero-divisor over `Z[G]` iff over `Z[H_4]`. A decision procedure over `G` would decide
  Zero-divisors-in-`Z[H_4]`, contradicting Corollary 5.
