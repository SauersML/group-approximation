---
rg: 2
id: order-two-universal-no-infinite-corner-proof
kind: route
title: Kill the integral symbol over the rational function field and finish in the binary finitary layer
target: order-two-universal-ring-has-no-infinite-corner
requires:
  - order-two-universal-ring-has-finitary-symbol-sequence
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

Suppose `p, x_0, x_1, y_0, y_1` were a certificate `(PIC1)` in `M_d(A_2)`.

**Step 1: the symbol dies.**  Apply the entrywise symbol map of `(OT2)`
to land in `M_d(D)`, `D = Z[z,z^(-1)]`, and then view the matrices over
the fraction field `K = Q(z)`.  On `V = bar p K^d` the certificate gives
maps

```text
X : V (+) V --> V,     Y : V --> V (+) V,     YX = 1,
```
so `X` is injective and `2 dim_K V <= dim_K V`, forcing `V = 0` and
`bar p = 0`.

**Step 2: the surviving corner is finite.**  By `(OT2)`, `bar p = 0`
places `p` in `M_d(M_fin(N,F_2))`, a matrix of finite support on `d`
rays.  Choose a finite coordinate set containing that support.  Every
element of `p M_d(A_2) p` has all rows and columns inside that set, and
the entries are two-torsion, so the whole corner is a subring of a
**finite** matrix algebra over `F_2`, with unit `p != 0`.

**Step 3: repeat in finite dimensions.**  On the nonzero
finite-dimensional `F_2`-space `W = p F_2^N` the certificate again gives
a split injection `W (+) W -> W`, so `2 dim W <= dim W` and `W = 0`,
contradicting `p != 0`.

Hence no certificate exists in any `M_d(A_2)`.

## The two consequences and the embedding no-go

Consequence 1 and 2 are immediate: the hypotheses of
`properly-infinite-corner-forces-non-mf-from-rank-two` and of
`elementary-rank-descent-to-two` both require exactly such an idempotent
(the latter at `p = 1`).

For the embedding no-go, let `iota : J_(F_2) -> A_2` be any ring map,
not assumed unital.  Every element of `J_(F_2)` is killed by two, so the
image is killed by two; by `(OT3)` and torsion-freeness of `D`, elements
of `A_2` killed by two have zero integral symbol and hence lie in
`M_fin(N,F_2)`.  So `iota(1)` is a finite-support idempotent `p'`, and
`iota(J_(F_2))` lies in `p' A_2 p'`, which by Step 2 is finite.  An
injective map from the infinite ring `J_(F_2)` into a finite ring is
impossible.  The same argument applies verbatim in every `M_d(A_2)`.
