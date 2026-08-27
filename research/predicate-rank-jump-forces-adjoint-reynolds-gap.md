---
rg: 2
id: predicate-rank-jump-forces-adjoint-reynolds-gap
kind: claim
title: Forbidden Schur-Clifford mass creates a quadratic-density adjoint Reynolds gap
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  predicate-rank-gate-doubles-restriction-multiplicity: that computes the restriction of one irreducible packet; this sums arbitrary packet multiplicities and converts forbidden Hilbert mass into a dimension-normalized projection-rank gap.
  finite-group-intertwiner-laplacian-gap: that gives a multiplicity-independent spectral gap for intertwiners of one fixed finite group; this computes a positive-density difference between the commutants of two nested packet groups inside one representation.
  scaled-kazhdan-transport: that transports asymptotic commutants through a one-sided compressor; this supplies the explicit positive-density commutant defect that such transport must eliminate.
---

Fix one predicate packet inclusion `A_f<=B_f`, let its assignment-independent
baseline spin dimension be `D=2^N`, and put `K=|f^(-1)(1)|`.  Let `rho` be an
exact finite-dimensional representation of `B_f`, compressed to its `J=-1`
sector `H_-` of dimension `d`.  Write `q` for the fraction of `H_-` carried by
selector sectors with `f(x)=1`.

Let `R_A,R_B` be the Reynolds orthogonal projections on the adjoint Hilbert
space `End(H_-)`, obtained by averaging conjugation by `rho(A_f)` and
`rho(B_f)`.  Since `A_f<=B_f`, `R_B<=R_A`, and

```text
rank(R_A-R_B)/d^2 >= (3/(4 D^2 K)) q^2.              (ARG1)
```

For the fixed-pivot support packet, `D=2` and `K=1`, so the explicit constant
is `3/16`.  Thus an extensive forbidden packet mass produces an extensive
adjoint projection defect without selecting individual irreducible copies or
using any ambient-dimension divisibility.
