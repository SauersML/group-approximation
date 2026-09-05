---
rg: 2
id: periodic-higman-algebraic-matrix-certificate
kind: claim
title: A degree-ten algebraic unit supplies the cyclic Higman matrix equations
artifacts:
  - research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md
  - experiments/periodic_higman_algebraic_certificate.py
---

There are a number field `F` of degree at most ten, an algebraic unit
`lambda` in `F` that is not a root of unity, and matrices

```text
A_j in SL_2(O_F[1/2])   (j in Z/4),
T = diag(lambda,1),
```

such that `T A_j T^-1 = [A_j,A_(j-1)]`, where the commutator is
`[a,b]=a^-1 b^-1 a b`. The upper-right entry of `A_j` is `i^j`, where
`i in F` satisfies `i^2=-1`. At every prime of `F` above two, `lambda`
reduces to one.

All matrices and the defining degree-five polynomial over `Z[i]` are
explicit in Sections 1–2 of the artifact.
The cyclic matrix equations already hold over the universal ring
`Z[i,1/2,L]/(P)`, so they specialize at any root of `P` in any field
of odd characteristic, with the displayed inverse for `L`.
