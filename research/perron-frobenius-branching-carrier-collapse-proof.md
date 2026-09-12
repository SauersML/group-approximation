---
rg: 2
id: perron-frobenius-branching-carrier-collapse-proof
kind: route
title: Orthogonal range capacity plus a Perron left eigenvector proves collapse
target: perron-frobenius-branching-carrier-collapse
requires: []
---

Fix a target `j`.  Write `R_(i,h)=T_(j,i,h)T_(j,i,h)^*`.  Traciality and
`T_(j,i,h)^*T_(j,i,h)=P_i` give

```text
tau(R_(i,h)) = tau(P_i)=x_i.
```

Moreover

```text
||(1-P_j)T_(j,i,h)||_2^2
 = tau(T_(j,i,h)^*(1-P_j)T_(j,i,h))
 = tau((1-P_j)R_(i,h))
 = x_i - tau(P_j R_(i,h)).
```

The range projections entering the fixed target `j` are pairwise orthogonal,
so their sum `R_j=sum_(i,h) R_(i,h)` is a projection and `R_j<=1`.  Hence

```text
sum_(i,h) tau(P_j R_(i,h))
 = tau(P_j R_j P_j)
 <= tau(P_j)=x_j.
```

Summing the preceding leakage identity therefore yields

```text
sum_i a_ji x_i - e_j <= x_j,
```

which is `(PF1)`.

Now restrict to a strongly connected component `C`.  Dropping terms entering
`C` from outside only decreases `(Ax)_j`, so

```text
x_C >= A_C x_C - e_C.
```

By Perron--Frobenius, the irreducible nonnegative matrix `A_C` has a strictly
positive left eigenvector `y` with

```text
y^T A_C = rho y^T.
```

Multiply the coordinate inequalities by `y_j` and sum.  This gives

```text
y^T x_C >= rho y^T x_C - y^T e_C,
```

or exactly

```text
(rho-1)y^T x_C <= y^T e_C.
```

If `rho>1`, zero leakage forces `y^T x_C=0`; positivity of `x` and `y` then
kills every carrier in the component.  The same inequality gives the stated
quantitative leakage floor whenever the Perron-weighted carrier mass stays
bounded below.