---
rg: 2
id: scalar-phase-core-retention-proof
kind: route
title: Evaluate the presentation energy on the scalar tuple and count inverse-pair multiplicities
target: scalar-phase-core-retention-forces-full-padding
requires:
  - inverse-conjugacy-padding-equals-multiplicity-defect
artifacts:
  - research/artifacts/retained-core-and-rank-countertests-2026-09-08.md
---

## Proof

**Admissibility.**  With `T = I` the Baumslag-Solitar relation reads
`R T R^(-1) = I = T^4`, so `(R, T)` is an exact `BS(1,4)` representation for
any unitary scalar `R`; `X = I` is a unitary.  In the square-free presentation
`S = R^(-1) T^2 R = I`, consistently with `T = S^2`.

**Energy.**  All four terms of `(FBR1)` are scalars times the identity:

```text
||X^2 - 1||_F^2         = 0,
||X R X - R^(-1)||_F^2  = d |e^(i theta) - e^(-i theta)|^2 = 4 d sin^2(theta),
||(X S^2)^3 - 1||_F^2   = 0,
||(X R S)^3 - 1||_F^2   = d |e^(3 i theta) - 1|^2 = 4 d sin^2(3 theta / 2),
```

giving `(SP2)`; the Taylor expansion is `4 theta^2 + 9 theta^2 + O(theta^4)`.

**Retention bound.**  Let `(X^, R^, T^)` be exact on `C^(d+k)` with
`R^ = R (+) R_new`.  From `X^^2 = 1` and `(X^ R^)^2 = 1` we get
`X^ R^ X^ R^ = 1`, i.e. `X^ R^ X^ = R^(-1)`, and `X^` is a unitary involution,
hence self-adjoint.  That is exactly `(IC1)`.  Since `0 < theta < pi`, the
values `e^(i theta)` and `e^(-i theta)` are distinct and neither is `+-1`, so
the prerequisite's count gives

```text
k >= k_min(R) = | m_R(e^(i theta)) - m_R(e^(-i theta)) | = d.
```

**Movement bound.**  The tuple `X = R = T = I_d` satisfies every relation of
the presentation, and `||R - I_d||_(2,d)^2 = |e^(i theta) - 1|^2 = 4 sin^2(theta/2)`,
which is `(SP4)`.  Since `E / d -> 0` while `k / (d + k) >= 1/2` for every
retaining completion, no bound of the form `k <= C E` can hold under
retention, whereas the displacement bound of `(FBR1)` holds with `k = 0`.
