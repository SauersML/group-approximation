---
rg: 2
id: thompson-v-direct-finiteness-failures-transfer-into-kernel
kind: claim
title: Direct-finiteness failures of the binary and ternary group algebras of Thompson's V transfer into the kernel of the Leavitt evaluation
distinct_from:
  leavitt-invisible-half-universal-over-every-finite-field: that transfers failures for a full Leavitt unit group, whose evaluation onto the Leavitt algebra is onto; this is the subgroup V, where the evaluation's image is only the span of prefix permutations, and it uses pure prefix permutations on disjoint cylinders.
  ternary-anti-central-failures-transfer-into-kernel-corners: that is the transfer for the anti-central summand of the ternary Leavitt unit group algebra; this is the transfer for F_2[V] and F_3[V], with no central element.
artifacts:
  - research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md
---

Let `p` be `2` or `3`, `S = F_p[V]`, `pi : S -> L_(F_p)(1,2)` the linear extension of the cylinder
embedding of `V`, and `K = ker pi`. There are a nonzero idempotent `q` in `K` and an injective
unital ring homomorphism `mu : S -> qSq` with `pi o mu = 0`.

So every pair `c a = 1 != a c` in `S` becomes the pair `(1-q) + mu(a)`, `(1-q) + mu(c)` inside
`1 + K`. `S`, `F_p 1 + K` and `qSq` are directly finite together, at every matrix size.

**Construction.**
- `p = 3`: `x` swaps the prefixes `00, 01`, `y` swaps `10, 11`, and `q = (1-x)(1-y)`.
- `p = 2`: `x` is a 3-cycle of three depth-3 prefixes inside `[0]`, `y` the same inside `[1]`, and
  `q = (x+x^2)(y+y^2)`.
- `mu(a) = delta_*(a) q`, with `delta(g) = sum_(|u|=k) S[u] g T[u]`: `k = 2` for `p = 3` and
  `k = 3` for `p = 2`.

Proof: Section 3 of the artifact, route `thompson-v-kernel-transfer-proof`.
