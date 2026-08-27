---
rg: 2
id: rfd-upgrades-relative-gap-failure-to-full-support-fd-witnesses
kind: route
title: Approximate one relative-gap witness by finite-dimensional coefficients and remove the trivial quotient summand
target: km-triangle-relative-gap-failure-has-fd-full-support-witnesses
requires:
  - km-triangle-relator-kernel-has-no-relative-gap
  - virtually-free-full-algebras-are-rfd
  - simple-kazhdan-kac-moody-lattices-exist
---

Fix finite `F subset G_0` and `epsilon>0`.  By
`km-triangle-relator-kernel-has-no-relative-gap`, after decreasing the
tolerance there are a unitary representation `pi` and a unit vector `v` such
that

```text
H_pi^K={0},       max_(g in F)||pi(g)v-v||<epsilon/16.     (1)
```

Because the closed convex hull of the `K`-orbit of `v` contains the
orthogonal projection of `v` onto `H_pi^K`, it contains `0`.  Consequently

```text
sup_(k in K)||pi(k)v-v||>=1;                               (2)
```

otherwise every convex combination of orbit vectors would remain at distance
strictly less than `1` from `v` and could not converge to `0`.  Choose
`k_0 in K` with `||pi(k_0)v-v||>3/4`.

Since `C^*(G_0)` is RFD, `pi` is weakly contained in the direct sum of the
finite-dimensional representations of `G_0`.  The coefficient of `v` can
therefore be approximated on the finite set needed to compute the displacement
norms for `F union {k_0}` by a coefficient of a finite direct sum of
finite-dimensional representations.  Indeed
`||pi(g)v-v||^2=2-2 Re <pi(g)v,v>`, and the same identity holds for the
approximating coefficient; including the identity in the finite set and then
normalizing its vector preserves the approximation.  Hence there are a finite-dimensional
representation `sigma` and a unit vector `w` such that

```text
max_(g in F)||sigma(g)w-w||<epsilon/8,
||sigma(k_0)w-w||>1/2.                                    (3)
```

Let `p` be the projection onto `H_sigma^K`.  Normality of `K` makes this a
`G_0`-invariant subspace.  The representation on it factors through
`Lambda`; every finite-dimensional representation of the infinite finitely
generated simple group `Lambda` is trivial.  Thus `pH` is exactly a trivial
`G_0`-summand.  Write `w=w_0+w_1` with `w_0=pw`.  Since `sigma(k_0)` fixes
`w_0`, the second inequality in `(3)` gives

```text
1/2<||sigma(k_0)w_1-w_1||<=2||w_1||,
```

so `||w_1||>1/4`.  The first inequality in `(3)` and triviality of `w_0`
give, for `g in F`,

```text
||sigma(g)w_1-w_1||=||sigma(g)w-w||<epsilon/8.             (4)
```

Restrict `sigma` to the invariant complement `(H_sigma^K)^perp`, call the
restriction `rho`, and put `xi=w_1/||w_1||`.  This representation has no
`K`-fixed vector, and `(4)` gives the bound in `(FDR2)` (indeed `<epsilon/2`).

For `(FDR3)`, in any finite-dimensional representation the complement
`1-z_rho` of the support of `rho(I)` is exactly the largest subspace on which
the representation factors through `G_0/K`; equivalently it is `H_rho^K`.
The latter is zero, so `z_rho=1`.

Finally fix `W`.  Apply `(FDR2)` with `F` containing `W` and all native
relators `n_j^(+-1)`.  For `x=a(n_j^(+-1)-1)b in B_W`, unitarity gives

```text
||rho(x)xi||
 =||(rho(n_j^(+-1))-1)rho(b)xi||
 <=||(rho(n_j^(+-1))-1)xi||+2||rho(b)xi-xi||.             (5)
```

The right side can be made arbitrarily small, simultaneously for the fixed
finite set `B_W`.  Summing its squares proves `(FDR5)`.
