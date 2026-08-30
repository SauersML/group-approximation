---
rg: 2
id: finite-normal-generator-hs-trivialization-proof
kind: route
title: Average bounded normal words onto the invariant projection
target: finite-normal-generator-hs-trivialization
requires: []
---

Let `S` be the finite conjugacy-invariant symmetric set of all conjugates of
`g` and `g^-1`.  Normal generation says `S` generates `G`; let `L` be the
diameter of `Cay(G,S)`.  Unitary conjugation invariance and

```text
||pi(g^-1)-1||_2=||pi(g)^*-1||_2=||pi(g)-1||_2
```

show that every `s in S` has defect `||pi(g)-1||_2`.  Write any `x in G` as
a product of at most `L` elements of `S`.  Unitary telescoping gives

```text
||pi(x)-1||_2<=L||pi(g)-1||_2.                        (1)
```

The finite-group Reynolds average is exactly the invariant projection:

```text
Q_pi=|G|^-1 sum_(x in G) pi(x).
```

Since `1-Q_pi` is a projection, `(1)` and the triangle inequality give

```text
sqrt(tr_d(1-Q_pi))
 =||1-Q_pi||_2
 <=|G|^-1 sum_x ||1-pi(x)||_2
 <=L||pi(g)-1||_2.
```

Squaring proves `(FNG-HS)`.