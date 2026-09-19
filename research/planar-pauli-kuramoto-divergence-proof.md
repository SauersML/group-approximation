---
rg: 2
id: planar-pauli-kuramoto-divergence-proof
kind: route
title: Evaluate the Pauli edge field through its complex order parameter
target: short-arc-planar-pauli-edges-have-uniform-divergence-gap
requires:
  - low-odd-square-removes-pairwise-green-stationarity
---

Pauli multiplication and `(LOS1)` give `(SAP1)`.  Put

```text
 z=(1/L)sum_j exp(ix_j)=R exp(i phi).
```

Then

```text
 d_i=-(i/2)R sin(phi-x_i)Y.                            (PPK1)
```

Relative to the midpoint of the containing interval every `x_i` has
distance at most `r/2`.  The projection of every `exp(ix_i)` on the midpoint
direction is therefore at least `cos(r/2)>=cos(r)`, so `R>=cos(r)`.

For `a_i=x_i-phi`, the identity
`sin(a_j-a_i)=sin(a_j)cos(a_i)-cos(a_j)sin(a_i)` gives

```text
 |sin(a_j-a_i)|<=|sin(a_i)|+|sin(a_j)|.
```

After squaring and averaging over `(i,j)`,

```text
 (1/L^2)sum_(i,j)sin^2(x_j-x_i)
 <=4(1/L)sum_i sin^2(phi-x_i).                         (PPK2)
```

The factor `1/4` in both edge and divergence energies, `(PPK1)`, and
`R>=cos(r)` prove `(SAP2)`.  Apply the scalar inequality on every central
block and integrate to obtain the direct-sum statement.
