---
rg: 2
id: atlas-q14-forces-t30-covariance-floor-proof
kind: route
title: Compare q14 with t20 and polar-round to the t30 commutant
target: atlas-q14-forces-t30-covariance-floor
requires:
  - atlas-a4-packet-centralizer-product-compiler
artifacts:
  - experiments/atlas_q14_t30_wall.py
---

The exact radius-five replay verifies `(Q14-1)--(Q14-2)` and verifies directly
that `q_14` has trivial image in the binary Leavitt algebra.  In the aligned
regular representation,

```text
q_14(U)=(rho(t23) U rho(t30) U^*)^2.                  (1)
```

If `V in C_30(k)`, equation `(1)` and `(Q14-2)` give

```text
q_14(V)=rho_k(t20).
```

The regular character vanishes at the nonidentity involution `t20`, so

```text
||q_14(V)-1||_2=sqrt(2).                              (2)
```

Only the two second-chart occurrences depend on the relative unitary.  For a
fixed unitary `A`, bi-invariance gives

```text
||UAU^*-VAV^*||_2<=2||U-V||_2.
```

Telescoping the two occurrences in `(1)` therefore gives

```text
||q_14(U)-q_14(V)||_2<=4||U-V||_2.                   (3)
```

Equations `(2)--(3)` and the reverse triangle inequality prove `(Q14-DIST)`.

It remains to compare distance and covariance without losing dimension.  Put
`h=h_k` and decompose its space into the `+1` and `-1` eigenspaces.  Relative
to this decomposition write

```text
U=[A B; C D].
```

If the ambient dimension is `N`, then

```text
c^2:=||UhU^*-h||_2^2
    =||Uh-hU||_2^2
    =(4/N)(||B||_F^2+||C||_F^2).                     (4)
```

Polar-round `A` and `D` to unitaries `A_0,D_0` on the two diagonal blocks,
extending their polar partial isometries on the kernels.  Every singular value
`sigma in [0,1]` obeys `(1-sigma)^2<=1-sigma^2`.  Hence, with
`V=diag(A_0,D_0) in C_30(k)`, unitarity of `U` gives

```text
||U-V||_2^2
 <=(1/N)[N_+-||A||_F^2+N_--||D||_F^2
          +||B||_F^2+||C||_F^2]
 =(2/N)(||B||_F^2+||C||_F^2)
 =c^2/2.                                               (5)
```

Taking the infimum in `(5)` proves `(Q14-COV)`.  Finally, since `h` is a
self-adjoint involution,

```text
||UhU^*-h||_2^2
 =2-2 Re tau_k(UhU^*h)=2x_30(U)^2.                   (6)
```

Combining `(Q14-DIST)`, `(Q14-COV)`, and `(6)` proves `(Q14-ROOT)` and the
three limiting bounds in `(Q14-WALL)`.
