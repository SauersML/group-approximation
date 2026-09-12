---
rg: 2
id: schur-near-idempotents-round-dimension-uniformly
kind: claim
title: Self-adjoint Schur near-idempotents round to conditional expectations with a dimension-free square-root bound
artifacts:
  - research/artifacts/schur-near-idempotent-partition-rounding-2026-09-08.md
---

Let `S=(s_ij)` be a real positive semidefinite `n` by `n`
matrix with `s_ii=1`, and let `P_S(X)=S circ X` be its Schur
channel on `M_n(C)`. Use normalized Hilbert--Schmidt norm and put

```text
delta = ||P_S^2-P_S||_(infinity->2).
```

There is a partition `Pi` of the coordinate set, with associated
unital block-diagonal algebra `A_Pi`, such that its
trace-preserving conditional expectation satisfies

```text
||P_S-E_(A_Pi)||_(infinity->2) <= min(1, 4 sqrt(delta)).
```

More precisely, for each `0<t<1/10` a partition can be chosen with

```text
||P_S-E_(A_Pi)||_(infinity->2)^2 <= 4 t^2 + 2 delta^2/t^2.
```

Thus the conclusion applies to every self-adjoint bistochastic
UCP Schur map, in its original matrix dimension. No estimate
of the dimension, the number of blocks, or the individual
matrix entries of the idempotence defect is required.

This is a restricted positive rounding theorem. It does not
assert that the native Kazhdan heat maps are Schur maps, or
that arbitrary self-adjoint bistochastic UCP near-idempotents
have such a rounding. In particular it does not establish the
native uniform heat-rounding premise or nonhyperlinearity.
