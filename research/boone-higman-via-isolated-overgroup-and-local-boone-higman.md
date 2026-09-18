---
rg: 2
id: boone-higman-via-isolated-overgroup-and-local-boone-higman
kind: route
title: Place the input in an isolated group, then realize that group's one existential sentence in a finitely presented simple group
target: boone-higman-conjecture
requires:
  - every-decidable-group-embeds-in-an-isolated-group
  - local-boone-higman-conjecture
  - isolated-embedding-is-one-existential-sentence
---

Let `G` be finitely generated with solvable word problem.
1. By `every-decidable-group-embeds-in-an-isolated-group`, `G ≤ H` with `H`
   isolated. `H` has solvable word problem (CGP arXiv:math/0511714, TeX lines
   704–706: "An isolated group has solvable word problem.").
2. `H` satisfies its own sentence `Σ_H` (presentation relators trivial,
   discriminating set nontrivial). By `local-boone-higman-conjecture`, `Σ_H` holds
   in some finitely presented simple group `S`.
3. By `isolated-embedding-is-one-existential-sentence`, `H ≤ S`, so `G ≤ S`.

The full argument, including the converse, is
`boone-higman-iff-isolated-hosts-and-local-boone-higman-proof`.

**The two open premises.**
- The first is about overgroups and does not mention simplicity.
- The second is about the universal theory of finitely presented simple groups:
  each finite piece may use a different host, and no overgroup is required.

Neither premise is known to imply the other, and the conjecture implies both. A
counterexample to the conjecture refutes one of them. On the second premise the
refutation is a finite certificate: a system `(E, N)` with a decidable model and
no model in any finitely presented simple group.
