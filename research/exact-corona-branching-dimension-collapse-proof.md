---
rg: 2
id: exact-corona-branching-dimension-collapse-proof
kind: route
title: Apply eventual coordinate ranks to a rational supercritical pressure vector
target: exact-corona-branching-dimension-collapse
requires:
  - matrix-corona-projection-monoid-is-rank-germs
  - rational-supercritical-branch-certificate
  - strongly-connected-branching-gives-rational-pressure
---

Let

```text
x_i=Dim_Q(p_i) in D_d^+.
```

Additivity, Murray--von Neumann invariance, `(ECB1)`, and `(ECB2)` give the
exact rank-germ equation

```text
x=A x.                                                         (ECP1)
```

There are only finitely many projection relations, so choose coordinate
projection lifts on one common cofinite tail.  If `r_(i,n)` is the rank of
the lift of `p_i`, then `(ECP1)` is the literal integer-vector equality

```text
r_n=A r_n                                                     (ECP2)
```

for every sufficiently large `n`.

Multiply `(ECP2)` by the positive rational vector `y`.  From `(ECB3)`,

```text
y.r_n=(A^T y).r_n >= (1+kappa)(y.r_n).
```

Both `kappa` and `y.r_n` are nonnegative, so `y.r_n=0`.  Positivity of every
coordinate of `y` gives `r_n=0`.  Thus every `p_i` has eventually zero rank,
and faithfulness of `Dim_Q` gives `(ECB4)`.

For irreducible `A` with spectral radius greater than one, a positive Perron
vector can be approximated from below by a rational subeigenvector with some
rational `kappa>0`.  Equivalently, the finite rational construction in
`strongly-connected-branching-gives-rational-pressure` supplies `(ECB3)`
directly when the branching system is strongly connected and has one genuine
branch.

For the marked-group statement, `(ECB4)` kills `e_z(rho)`.  The finite-order
functional-calculus identity `(ECB6)` then gives `rho(z)=1`.  Intersecting the
kernels of all norm-corona homomorphisms proves `(ECB7)`.  The MF radical is
normal, so a normally generating `z` forces the full-radical conclusion.
