---
rg: 2
id: stw81-positive-scalar-order-zero-approximation-is-scalar
kind: claim
title: One-colour approximation of a positive scalar identity map forces a projectionless algebra to be scalar
distinct_from:
  stw81-projectionless-rotating-overlap-degeneracy: that theorem turns two cross-orthogonal near-unital frames into a small colour; the present theorem identifies the endpoint after that colour is removed, even when the surviving map approximates only `c` times the identity for `0<c<1`.
artifacts:
  - research/artifacts/stw81-positive-scalar-order-zero-audit-2026-08-30.md
---

Let `D` be a unital projectionless C-star algebra and fix `c>0`.  Suppose
that for every finite set `E` in the unit ball and every `epsilon>0` there
are a finite-dimensional C-star algebra `F` and c.p.c. maps

```text
D --psi--> F --phi--> D                              (PSO1)
```

such that `phi` is order zero and

```text
norm(phi psi(a)-ca)<epsilon            (a in E).      (PSO2)
```

Then

```text
D=C1_D.                                                (PSO3)
```

Equivalently, for every nontrivial unital projectionless algebra and every
`c>0`, the completely positive map `c id_D` does not have nuclear dimension
zero.  Contractivity of both maps in (PSO1) is essential to the formulation,
but no nuclearity, simplicity, trace, or uniformity in `c` is required.

DERIVATION
[[stw81-invertible-order-zero-support-collapses-stage]]
