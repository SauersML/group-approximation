---
rg: 2
id: iwahori-hecke-square-spectral-separation-proof
kind: route
title: Satake-root moduli put the Hecke square on a segment and a disjoint ellipse
target: iwahori-hecke-square-separates-cuspidal-and-eisenstein
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Let `alpha,beta` be the two Satake roots of one simultaneous Hecke
eigenclass.  With the unnormalised weight-two convention,

```text
T_2 = alpha+beta,             alpha beta = 2 <2>,
```

so the eigenvalue of `K_2` is

```text
k(alpha,beta)
 = (alpha+beta)^2/(alpha beta)
 = 2 + alpha/beta + beta/alpha.                         (HSP2)
```

For a cuspidal class Deligne gives `|alpha|=|beta|=sqrt(2)`.  Writing
`alpha/beta=e^(i theta)`, `(HSP2)` becomes `2+2 cos(theta)`, and hence lies
in `[0,4]`.

For a weight-two Eisenstein class the two unramified roots have moduli
`1` and `2`.  Thus, after interchanging them if necessary,
`alpha/beta=2e^(i theta)`, and `(HSP2)` is

```text
2+(5/2)cos(theta)+(3/2)i sin(theta).                    (HSP3)
```

This is the ellipse centred at `2` with horizontal and vertical semiaxes
`5/2` and `3/2`.

The distance from `(HSP3)` to `[0,4]` is at least `1/2`.  Indeed, writing
`c=cos(theta)`, when `|c|<=4/5` the vertical distance is at least `9/10`.
For `c>=4/5` the squared distance to the endpoint `4` is
`25/4-10c+4c^2`, whose minimum on that interval is `1/4` at `c=1`; the
other endpoint is symmetric.  Equality occurs at the two real tips
`-1/2` and `9/2`.

Oldforms, deck-group isotypic components, and tensoring by the coefficient
space do not change this local Satake-root calculation.  On the Iwahori
edge, the Bernstein-central element with the same symmetric Satake
polynomial has the same two spectral sets.  This proves the algebraic
separation.  It deliberately does **not** assert a uniform norm for the
Riesz projections: Eisenstein cohomology is not square-integrable, and
identifying the algebraic Hecke involution with the cellular positive
adjoint there is precisely the nonnormality issue left open.
