---
rg: 2
id: exact-corona-branching-dimension-collapse
kind: claim
title: A supercritical finite branching system of corona projections vanishes exactly
root: true
artifacts:
  - research/exact-corona-branching-dimension-collapse-proof.md
---

Fix a norm matrix corona

```text
Q_d=(prod_n M_(d_n)(C))/(directSum_n M_(d_n)(C)).
```

Let `A=(a_ij)` be a finite nonnegative integer matrix.  An exact
`A`-branching system in the stable projection monoid of `Q_d` consists of
stable projections `p_1,...,p_N` and, for every `i`, an orthogonal
decomposition

```text
p_i = directSum_(j=1)^N directSum_(h=1)^(a_ij) q_(i,j,h),       (ECB1)
```

with

```text
q_(i,j,h) ~MvN p_j.                                            (ECB2)
```

If there are `y in Q_(>0)^N` and `kappa in Q_(>0)` such that

```text
A^T y >= (1+kappa)y,                                           (ECB3)
```

then

```text
p_1=...=p_N=0.                                                 (ECB4)
```

In particular `(ECB4)` holds whenever `A` is irreducible and has
Perron--Frobenius spectral radius greater than one.  For an integer
branching matrix, it is enough that the directed branching system is strongly
connected, every state has an outgoing branch, and at least one state has two
outgoing branches counted with multiplicity.

The conclusion is insensitive to stabilization and to arbitrarily sparse
coordinate support.  It uses eventual coordinate ranks, so a nonzero
projection cannot evade the certificate by occupying a vanishing proportion
of the ambient matrices.

### Marked-group consequence

Let `G` be countable and let `z in G` have finite order `m>=2`.  For a corona
homomorphism `rho:G->U(Q_d)`, put

```text
e_z(rho)=1-(1/m)sum_(h=0)^(m-1) rho(z)^h.                       (ECB5)
```

This is the active spectral projection of `rho(z)`, and

```text
e_z(rho)=0  iff  rho(z)=1.                                     (ECB6)
```

Suppose one fixed matrix `A` satisfying `(ECB3)` has the following property:
for every `d` and every `rho`, the projection `e_z(rho)` occurs among the
projections of an exact `A`-branching system.  Then

```text
z in Rad_MF(G).                                                 (ECB7)
```

If `z` normally generates `G`, then `Rad_MF(G)=G`.  Thus a finite exact
projection-branching certificate can prove total MF collapse without any
estimate depending on the coordinate dimensions.
