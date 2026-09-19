---
rg: 2
id: stw99-xcix-global-central-defect-modulus-proof
kind: route
title: Diagonalize zero defects and transport arbitrary finite windows in both directions
target: stw99-xcix-global-central-defect-modulus
requires:
  - stw99-xcix-central-copy-transfer-bound
  - stw99-xcix-fixed-centrality-windows-collapse-at-zero-distance
---

Every commutator of contractions has norm at most `2`, so (K1), including
the empty-embedding convention, takes values in `[0,2]`.

Suppose first that the separable unital algebra `E` is Z-stable.  The
approximately central embedding characterization of absorption by a
strongly self-absorbing algebra says that, for every finite subset of `E`,
every finite subset of `Z`, and every positive tolerance, there is a unital
embedding `Z->E` with all the requested commutators below that tolerance.
Consequently every `Delta_(m,k)(E)` is zero, and hence `kappa_Z(E)=0`.

Conversely, suppose `kappa_Z(E)=0`.  Choose a dense sequence `(e_i)` in the
unit ball of `E`.  For each `n`, the equality
`Delta_(n,n)(E)=0` supplies a unital embedding

```text
rho_n:Z->E
```

such that

```text
max_(i,j<=n) norm([rho_n(z_j),e_i])<1/n.              (P1)
```

The coordinatewise map gives a unital embedding

```text
rho:Z->E_infinity,       rho(z)=[(rho_n(z))_n].       (P2)
```

Equation (P1), density, and the commutator Lipschitz estimate put its range
in `E_infinity intersect E'`.  The central-sequence characterization of
absorption now shows that `E` is Z-stable.  This proves (K2).

For the metric estimate, first suppose that `A` contains a unital copy of
`Z`.  Fix `m,k` and contractions `x_1,...,x_m in B`.  Choose contractions
`a_i in A` with

```text
norm(x_i-a_i)<gamma.
```

Given `eta>0`, choose a unital embedding `psi:Z->A` for which

```text
max_(i<=m,j<=k) norm([psi(z_j),a_i])
 < Delta_(m,k)(A)+eta.                               (P3)
```

The central-copy transport bound supplies an embedding `phi:Z->B` and

```text
max_(i<=m,j<=k) norm([phi(z_j),x_i])
 < Delta_(m,k)(A)+eta+304 sqrt(gamma)+2 gamma.        (P4)
```

Because `z_1=1_Z`, the transport estimate also puts the projection
`phi(1_Z)` within `152 sqrt(gamma)<1` of the common unit
`psi(1_Z)=1`.  A proper subprojection of the unit is exactly distance one
from it, so `phi(1_Z)=1`; thus `phi` is unital.  In particular `B` contains
a unital copy of `Z`.

Take the infimum in (P4), then the supremum over the tuple `(x_i)`, and let
`eta` tend to zero.  This gives

```text
Delta_(m,k)(B)
 <= Delta_(m,k)(A)+304 sqrt(gamma)+2 gamma.           (P5)
```

Taking the supremum over `m,k` proves the corresponding one-sided estimate
for `kappa_Z`.  Since `B` now contains a unital copy, interchange `A` and
`B` and repeat the argument.  The Kadison--Kastler distance is symmetric,
so the reverse estimate has the same constant.  This proves (K3).  The case
where the initial copy lies in `B` is identical with the roles reversed.

If `A` is Z-stable, (K2) and (K3) give (K4).  Finally, for a sequence of
unital counterexample pairs with `gamma_n->0`, (K2) makes each target defect
strictly positive while (K4) makes it converge to zero.
