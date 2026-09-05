---
rg: 2
id: compressed-irreducibles-require-all-deleted-dimensions
kind: claim
title: Close exact corrections of compressed irreducibles must restore every deleted dimension
artifacts:
  - research/artifacts/compressed-representation-quadratic-curvature-2026-09-05.md
distinct_from:
  direct-sum-weil-compressions-have-quadratic-padding: that supplies an upper padding ledger for a special direct sum of Weil compressions; this forces every close correction of any irreducible Kazhdan representation to recover all deleted dimensions.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that excludes qualitative same-dimension stability; this gives an explicit obstruction at every intermediate dimension and a sharp quadratic padding scale in the all-H2 case.
---

Let `G=<S|R>` have a finite symmetric Kazhdan generating set S with
constant kappa, in the convention
`dist(v,H^G)<=kappa^(-1)max_s||pi(s)v-v||`. Write ell for the maximal
defining-relator length. Let `rho:G->U(N)` be irreducible, remove any
`k<N` dimensions, put `d=N-k`, and polar-round the compressed
generators to a tuple `U:S->U(d)`, consistently on inverse letters.

The normalized-HS defining defect delta obeys

```text
rank(U(r)-I)<=|r|k,
d delta^2<=2 ell^2 k.                                  (CID1)
```

For every intermediate dimension `d<=D<N` and every exact representation
`sigma:G->U(D)`, in every unitary identification of its coordinates,

```text
max_s||sigma(s)-(U_s direct_sum I_(D-d))||_(2,D)
 >= kappa-sqrt((2k+4(D-d))/D)
 >= kappa-sqrt(6k/d).                                  (CID2)
```

Restoring all k dimensions is sufficient: the original representation
rho has generator distance at most `sqrt(6k/N)` from `U direct_sum I_k`.
Thus for a sequence with `k=o(N)`, every exact padded correction with
error tending to zero eventually has `D>=N`. Its necessary relative
padding is at least

```text
(D-d)/d >= k/d >= delta^2/(2 ell^2).                    (CID3)
```

No uniform relative-padding bound `o(delta^2)` can hold for these inputs.
For growing k, `(CID1)` alone does not give comparability between
`d delta^2` and k.

There is a sharp all-H2 specialization. Assume in addition ordinary
Hilbert H2 vanishes for every unitary representation and take `k=1`
with N tending to infinity. Then constants `c,C>0` independent of N
satisfy eventually

```text
c <= d delta^2 <= C.                                   (CID4)
```

Consequently the necessary one-dimensional padding has relative size
comparable to `delta^2`. The hypotheses have explicit instances in
`SL_5(Z)`: its finite projective-point permutation representations have
irreducible mean-zero summands of dimensions `p^4+p^3+p^2+p`, for primes p.
This is a sharp test for the correction program, not a construction of
an exact dilation for arbitrary approximate representations.

DERIVATION
compressed-intertwiner-gap-and-rank-integrality-proof
