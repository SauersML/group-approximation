---
rg: 2
id: perron-frobenius-branching-carrier-collapse
kind: claim
title: Supercritical finite branching forces carrier mass to pay leakage
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  Fix projections
`P_1,...,P_m` and a nonnegative integer matrix `A=(a_ji)`.  For every ordered
pair `(j,i)` and every `1<=h<=a_ji`, suppose there is a partial isometry
`T_(j,i,h)` with

```text
T_(j,i,h)^* T_(j,i,h) = P_i.
```

For each fixed target `j`, assume all range projections

```text
R_(j,i,h)=T_(j,i,h) T_(j,i,h)^*
```

are pairwise orthogonal as `(i,h)` varies.  Define target leakage

```text
e_j = sum_(i,h) ||(1-P_j) T_(j,i,h)||_2^2
```

and carrier masses `x_j=tau(P_j)`.

Then

```text
x >= A x - e                                                   (PF1)
```

coordinatewise.  Consequently, if one strongly connected component of `A`
has Perron--Frobenius eigenvalue `rho>1` and `y>0` is a left Perron vector on
that component, then

```text
(rho-1) sum_j y_j x_j <= sum_j y_j e_j.                        (PF2)
```

In particular an exact zero-leakage realization of a supercritical component
has zero carrier mass there.  Quantitatively, any fixed positive lower bound on
the Perron-weighted carrier mass forces a fixed positive leakage floor.

The one-cut/Hall contradiction is the one-vertex special case `A=[2]`.  The
point of `(PF2)` is that one does **not** need both branches to return to the
same coefficient cut: a finite cycle of different coefficient sectors already
collapses whenever its branching matrix has spectral radius greater than one.