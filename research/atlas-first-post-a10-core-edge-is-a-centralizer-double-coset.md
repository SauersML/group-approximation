---
rg: 2
id: atlas-first-post-a10-core-edge-is-a-centralizer-double-coset
kind: claim
title: The first core edge beyond the A10 rung is one explicit centralizer double-coset intersection
artifacts:
  - research/artifacts/atlas-a4-first-post-a10-core-edge.json
  - research/atlas-a10-next-core-edge-double-coset-proof.md
distinct_from:
  atlas-forward-collision-a10-absorbs-both-full-charts: that constructs the two full chart extensions but imposes no new cross edge; this gives the exact necessary-and-sufficient permutation equation for the first new edge.
  atlas-one-forward-c3-has-no-standard-gl6-completion: that fixes a tiny binary-linear representation class; this ranges over every regular-permutation alignment at the A10 multiplicity.
---

Fix the regular A10 carrier and the two full regular A8 extensions of
`atlas-forward-collision-a10-absorbs-both-full-charts`.  Let

```text
x = first-chart s
  = 01000000010100000000010000000001       (order 2),
y = second-chart r^-1
  = 00010000010100000000010000000001       (order 3).
```

The next distinct large-component core edge can be added by permutation
alignments if and only if there exists

```text
W in C_(S_N)(F) C_(S_N)(K),       N=1814400,
```

such that

```text
(x W y W^-1)^3=1.                                  (DC1)
```

Here `x,y` denote their matrices in any fixed reference `90 Reg(A8)` chart
extensions.  Thus the post-A10 seam is a single labeled centralizer-product
intersection, not a search over arbitrary `S_N` permutations.

No assertion that `(DC1)` is empty or nonempty is made here.
