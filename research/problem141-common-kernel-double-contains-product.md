---
rg: 2
id: problem141-common-kernel-double-contains-product
kind: claim
title: A symmetric amalgam double over a proper subgroup containing a normal kernel contains that kernel times Z
artifacts:
  - research/artifacts/problem141-user-document-integration-2026-09-20.md
distinct_from:
  fibre-split-amalgam-kernels-are-free-and-centralize-the-fibre: that assumes compatible complements over a common normal fibre and computes the kernel of an amalgam map to a common extension; this requires no complements and embeds N times Z directly into a symmetric double
  kt-double-is-nielsen-semidirect-product: that states a free fold-kernel decomposition for the binary Kun--Thom pair; this states the direct-product subgroup for every symmetric double with a common normal subgroup
  compressed-doubles-raise-cohomological-dimension: that gives a cohomological-dimension bound from a compressor of the entire edge group; this gives an explicit direct-product subgroup from a normal subgroup contained in the edge, without a dimension or compression assumption on the edge itself
---

Let `N` be a normal subgroup of a group `P`, and let
`N <= Lambda < P`, with `Lambda` proper. Form the symmetric amalgam
`D=P *_Lambda P`, using the identical inclusion of `Lambda` in both
copies, and write `j_1,j_2:P->D` for the canonical embeddings.

For every `t in P minus Lambda`, the element

```
s=j_2(t)^(-1) j_1(t)
```

has infinite order, centralizes the common embedded copy of `N`, and
has trivial cyclic-subgroup intersection with that copy. Consequently

```
N x Z -> D,  (n,m) |-> j_1(n) s^m
```

is an injective homomorphism. If `N` contains an infinite-order element,
then `D` contains `Z^2` and is not word-hyperbolic.

No splitting of `P->P/N`, finite generation, torsion-freeness, residual
finiteness, or approximation hypothesis is required. Normality is in
`P`, not merely in `Lambda`, and the two edge inclusions are the same.

**Attribution:** this statement and the element `s` were supplied by the
user in the Problem 141 proof attempt; the proof below records and checks
that argument. No agent discovery or historical-priority claim is made.

Proof: [[problem141-common-kernel-double-contains-product-proof]].
