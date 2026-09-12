---
rg: 2
id: binary-tetrahedral-free-conjugate-hull-proof
kind: route
title: Use one quaternion conjugate and the infinite dihedral fixed-space test
target: binary-tetrahedral-packet-hull-saturates-unprotected-seed-sign
requires:
  - binary-tetrahedral-conditional-e5-root-bridge
  - finite-pauli-seed-reducing-quarter-carrier
---

Let `G=G_1 *_A G_2` be the amalgam in `(BTB2)`, with the Pauli seed sign
`B_0 in G_1\A` and a quaternion element `t in G_2\A`.  An alternating word
in `B_0` and `tB_0t^(-1)` expands to an alternating amalgam normal form,
because every occurrence of `B_0` and `t` lies outside `A`.  Thus the two
involutions generate their free product and `r=B_0tB_0t^(-1)` has infinite
order.

If `P,Q` are the positive spectral projections of the two involutions, then

```text
1-(P join Q)=(1-P) meet (1-Q).
```

Every vector in the right side is fixed by `r`.  The left regular
representation of an infinite-order element has zero fixed space, proving
`P join Q=1`.  Multiplication by the central projection
`c=q_J^-q_ell^-` proves `(BHS3)--(BHS4)`.

For canonical microstates use the Cesaro polynomial

```text
A_N=N^(-1)sum_(k=0)^(N-1)rho(r)^k.
```

It is the identity on `Fix(r)`, so

```text
tr(P_Fix(r))<=||A_N||_2^2.
```

For fixed `N`, canonical moment convergence and nontriviality of
`r^(j-k)` give

```text
lim ||A_N||_2^2=1/N.
```

Letting `N` grow proves the asymptotic statement.  The direct-product
enlargement `(BHS6)` is an injective amalgam whenever the protected finite
packet commutes with `H,Z,ell`; sending the root, `ell`, and the auxiliary
factor to one still gives the perfect-model extension.
