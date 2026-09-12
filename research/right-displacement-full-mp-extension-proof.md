---
rg: 2
id: right-displacement-full-mp-extension-proof
kind: route
title: Decompose the complexified Jacobian by right displacement
target: right-displacement-reynolds-scalar-cb-complete
requires: []
---

On `B(l2(Q))`, the matrix diagonals

```text
{M_f rho(z):f in l_infinity(Q)},   z in Q,
```

are mutually orthogonal Hilbert--Schmidt fibers.  Conjugation by a left
translation preserves every fiber and acts there as the same left
translation of `f`.  After complexifying the anti-Hermitian tangent, all
fixed-space projections, odd-space projections, and cubic Reynolds rows are
therefore copies of one scalar column.  Orthogonal direct-sum functional
calculus shows that the full Hilbert-space Moore--Penrose extension is the
coefficientwise lift of the scalar one.

The scalar extension belongs to the finite left group algebra and hence has
rows `T_j=sum_g a_(j,g)L_g`.  Lifting gives

```text
sum_(j,g) a_(j,g) Ad(lambda(g)).
```

The triangle inequality bounds its cb norm by `sum_(j,g)|a_(j,g)|`.  On the
diagonal scalar subspace, choose independently at one output point the phases
of the two input functions at the distinct points `g^(-1)q`; this gives the
reverse inequality.  Thus the scalar infinity norm, scalar cb norm, and full
matrix cb norm of these full-space extensions agree.  Corners belonging to
arbitrary finite-dimensional representations reduce all the conjugations and
their adjoints, so restriction cannot increase the norm.

The phase witness uses arbitrary two-row inputs.  It proves no equality with
the norm of the inverse restricted to its range, and the target records this
scope explicitly.
