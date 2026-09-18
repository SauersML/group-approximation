---
rg: 2
id: fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu
kind: claim
title: On a regular tree times an infinite amenable Cayley graph, and on the lamplighter over a tree, the l2 boundedness threshold equals the uniqueness threshold
distinct_from:
  fpbs-hp-uniqueness-and-long-range-order: that imports Hutchcroft--Pan arXiv:2409.12283 on relative uniqueness along a subgroup; this imports a different paper, arXiv:2412.15895, on the equality p_(2->2) = p_u for tree products
  fpbs-relative-threshold-is-quotient-l2-threshold: that cites the same theorem as evidence for its Claim E (item 3 of its Evidence) without a citation node; this is the citation node, with the verbatim statement and the definitions it uses
  fpbs-tree-projected-square-root-fibre-law-below-pu: that is the open extension of p_(2->2) = p_u to non-product tree-projected generating sets; this is the known product case
---

**ESTABLISHED (imported).** Proof route:
`fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu-cite`.

**Setting.**

- Let `T` be the `k`-regular tree, with `k >= 3`.
- Let `H` be an infinite amenable Cayley graph.
- `T x H` is the Cartesian product. Two vertices are adjacent when they agree
  in one coordinate and are adjacent in the other.
- `T_p` is the matrix `T_p(x,y) = tau_p(x,y) = P_p(x <-> y)`.
- `p_(2->2) = sup{p in [0,1] : ||T_p||_(2->2) < infinity}`.

These are the paper's definitions, and they agree with the board's.

**Theorem (Hutchcroft--Pan, arXiv:2412.15895v1, Theorem 1.2).** If `G` is
`LL(T)` (the lamplighter over `T`) or `T x H`, then

```text
p_(2->2)(G) = p_u(G).
```

**Supplement (same paper, abstract).** For `T x Z^d` with `d >= 1`,

```text
0 < p_c < p_u < 1.
```

The paper cites this as known, and it is not a new result there.

**Cayley structure.** `T` is the Cayley graph of `(Z/2)^{*k}` on its `k`
standard involutions, and it is simple and `k`-regular. `Z^d` is the Cayley
graph of `Z^d` on `{±e_i}`. So `T x Z^d` is the simple Cayley graph of the
nonamenable group `(Z/2)^{*k} x Z^d` on the disjoint union of the two
generating sets. For `k = 4` the tree is also `Cay(F_2, {a^±, b^±})`, which
gives the standard Cayley graph of `F_2 x Z^d`.

Status records an imported theorem, not independent mathematical verification.
