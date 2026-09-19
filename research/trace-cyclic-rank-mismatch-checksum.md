---
rg: 2
id: trace-cyclic-rank-mismatch-checksum
kind: claim
title: Two cyclic products charge every finite-dimensional normalized-rank mismatch
distinct_from:
  approximate-relative-leavitt-cell-kills-active-trace: that applies cyclicity to the three relations of one decoded binary Leavitt cell; this isolates the general two-carrier scalar checksum and its adjoint/amplification form.
  five-fourths-projection-surplus-pays-linear-hs-energy: that charges excess total projection mass against a capacity bound; this needs only equality of the two cyclic traces.
  adjoint-reynolds-rank-gap-pays-every-return: that starts with two packet Reynolds projections and a returned copy; this is the general finite-matrix conservation law used after such carriers have been decoded.
artifacts:
  - research/artifacts/crispr-self-hash-compiler-2026-08-20.md
---

Let `E,F in M_d(C)` be projections and let `X,Y in M_d(C)` be arbitrary.
If

```text
|tr_d(YX)-tr_d(E)|<=epsilon,
|tr_d(XY)-tr_d(F)|<=delta,                              (TCM1)
```

then

```text
|tr_d(E)-tr_d(F)|<=epsilon+delta.                       (TCM2)
```

The stronger hypotheses

```text
||YX-E||_2<=epsilon,       ||XY-F||_2<=delta             (TCM3)
```

imply `(TCM1)` and hence `(TCM2)`.  In particular, if `P<=E` and
`F=E-P`, then

```text
tr_d(P)<=epsilon+delta.                                  (TCM4)
```

Every assertion is unchanged by common spectator amplification
`A |-> A tensor I_k`: normalized traces and normalized Hilbert--Schmidt
errors are unchanged.

The same theorem applies on the adjoint Hilbert space `M_d(C)`, of dimension
`d^2`, with normalized linear trace on `End(M_d)`.  If packet Reynolds
projections acquire a spectator factor, their ranks and the ambient adjoint
dimension both acquire the same factor `k^2`, so the normalized mismatch in
`(TCM2)` is again unchanged.

This is the finite-dimensional self-hash principle: the payload is not
watched by an independent register; it is the missing rank in a conservation
law which finite matrices satisfy automatically.  It does not construct the
group-word maps `X,Y`, and it must not be promoted to a universal tracial
identity in an exact infinite witness algebra.
