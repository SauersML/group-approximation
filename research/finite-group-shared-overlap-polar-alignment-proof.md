---
rg: 2
id: finite-group-shared-overlap-polar-alignment-proof
kind: route
title: Average the overlap partial isometry and threshold its polar part
target: finite-group-shared-overlap-polar-alignment
requires: []
---

Put `T=V_2 V_1^*` and average it onto the exact intertwiner space:

```text
T_bar=(1/|A|) sum_(a in A) rho_2(a) T rho_1(a)^*.
```

Changing variables in the sum gives

```text
rho_2(b) T_bar=T_bar rho_1(b)                                   (OPA2)
```

for every `b in A`. For each summand, insert
`V_2 f(a)f(a)^*V_1^*=T`; the two resulting errors are exactly the two
intertwining defects. Triangle inequality followed by Cauchy--Schwarz in the
average gives

```text
||T_bar-T||_F <= (eta_1+eta_2) sqrt(d)=eta sqrt(d).               (OPA3)
```

The singular values of `T` are `1` with multiplicity `d` and `0` otherwise.
Mirsky's singular-value inequality and `(OPA3)` imply that fewer than
`4 eta^2 d` of the first `d` singular values of `T_bar` can be below `1/2`.
Therefore

```text
K_1=1_[1/2,infinity)(|T_bar|) C^(m_1)
```

has dimension at least `(1-4 eta^2)d`.

Equation `(OPA2)` implies that `|T_bar|` commutes with `rho_1(A)`, so `K_1`
is invariant. In the polar decomposition `T_bar=W_0|T_bar|`, the polar part
intertwines on the support of `|T_bar|`. Restrict `W_0` to `K_1` and set
`K_2=W_0K_1`. This restriction is unitary from `K_1` to `K_2`, both spaces
are invariant, and `(OPA2)` gives the asserted exact intertwining relation.
