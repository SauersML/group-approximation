---
rg: 2
id: atlas-six-relator-leavitt-regular-trace-countermodel-proof
kind: route
title: Spend the internal Leavitt chart conjugator on the surviving rank-three bridge
target: atlas-six-relator-leavitt-tracial-countermodel
requires:
  - atlas-charts-overlap-trivially
  - leavitt-factor-regular-charts-inner-conjugate
  - regular-atlas-linearized-h-coercivity
---

All six displayed words are genuine Leavitt-kernel words, so they evaluate
to the identity in `Q`.  Put `M=L(Q)`.  By
`leavitt-factor-regular-charts-inner-conjugate` there is an internal unitary
`U in M` such that

```text
U lambda_Q(i_1(a)) U^*=lambda_Q(i_2(a))       (a in A8). (SLTC2)
```

Thus this is exactly the common-orbit phase model inside the finite factor
`M`, and all six nonlinear defects vanish.

The two marked copies of `H=GL_3(2)` do not agree in `Q`: otherwise their
common nonidentity elements would lie in the intersection of the two marked
`A8` subgroups, contradicting `atlas-charts-overlap-trivially`.  Hence some
standard generator `t` of `H` has nontrivial bridge

```text
b_t=i_2(t)i_1(t)^-1 != 1 in Q.
```

In the canonical trace,

```text
||lambda_Q(b_t)-1||_2=sqrt(2),                        (SLTC3)
```

and under `(SLTC2)` this is precisely the corresponding covariance defect

```text
||rho(t)U rho(t)^*-U||_2.
```

The finite-dimensional operator inequality underlying
`regular-atlas-linearized-h-coercivity` is a positive operator inequality in
the finite-dimensional group algebra of `A8`: the regular representation is
faithful on that algebra.  It therefore holds in every unitary
representation of `A8`, including the conjugation representation on
`L^2(M)`.  Applying it to the vector `U` shows

```text
0 < sum_t ||rho(t)U rho(t)^*-U||_2^2
  <= C_lin sum_j l_j(U)^2.
```

This proves `(SLTC1)`.
