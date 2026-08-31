---
rg: 2
id: su2-clock-field-has-zero-router-energy-proof
kind: route
title: Wind one full SU(2) torus turn around a cyclic router
target: long-router-square-energy-cannot-control-endpoint-frame
requires:
  - head-retention-forces-distance-from-every-global-frame
---

Let `e_0,...,e_(L-1)` be the standard basis of `C^L`, with indices
modulo `L`. Define

```text
C_L(e_j tensor z)=e_(j+1) tensor z,
R(theta)=diag(exp(i theta),exp(-i theta)) in SU(2),

W_L(e_j tensor z)=e_j tensor R(2pi j/L)z.               (SCF1)
```

The shift changes every block angle by the same increment:

```text
C_LW_LC_L^(-1)
 = (I_L tensor R(-2pi/L))W_L.                           (SCF2)
```

For the normalized Hilbert--Schmidt norm on two-by-two matrices,

```text
||R(theta)-I||_2^2
 =(1/2)(|exp(i theta)-1|^2+|exp(-i theta)-1|^2)
 =4 sin^2(theta/2).                                    (SCF3)
```

Equations `(SCF2)--(SCF3)` give `(LRS1)`. Every adjacent pair of
conjugates has the same distance, so summing the squares over `L/2`
edges gives

```text
(L/2)*4 sin^2(pi/L)=2L sin^2(pi/L),
```

which tends to zero. This is `(LRS2)`.

At half a turn,

```text
C_L^(L/2)W_LC_L^(-L/2)
 =(I_L tensor R(-pi))W_L
 =-W_L.
```

Therefore the endpoint difference is `-2W_L` and has normalized
Hilbert--Schmidt norm exactly `2`, proving `(LRS3)`.

If `(LRS4)` held with one constant `B`, its left side would equal `4`
while its right side would tend to zero, a contradiction. The same
example shows why Cauchy--Schwarz introduces a factor proportional to the
router length:

```text
||endpoint difference||_2^2
 <= (L/2) sum_(router edges)||edge difference||_2^2.
```

That factor is sharp in order. The construction uses determinant-one,
non-scalar two-by-two rotations, so it is not a scalar rephasing. It is
still only a local-covariance counterexample: the rotations do not satisfy
the full Jacobson presentation, consistent with
`jacobson-projective-two-sheet-actions-collapse`.
