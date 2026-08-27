---
rg: 2
id: kazhdan-centralizer-capture-forces-most-block-gaps-proof
kind: route
title: Aggregate bad minimal corners and contradict property (T) in the L2 ultraproduct
target: kazhdan-centralizer-capture-forces-most-block-gaps
requires: []
---

Let `B_n` be the set of bad minimal projections and put

```text
beta_n = sum_(j in B_n) tau_n(p_(n,j)).
```

Suppose `beta_n` does not tend to zero along `omega`.  After restricting to an
`omega`-large set there is `eta>0` with `beta_n >= eta`.

For each bad `p=p_(n,j)`, choose a self-adjoint witness `x_(n,j)` with

```text
tau_(n,p)(x_(n,j)) = 0,
||x_(n,j)||_(2,p) = 1,
sum_s ||[g_(s,n),x_(n,j)]||_(2,p)^2 < kappa^2/4.
```

The projections `p_(n,j)` lie in the exact joint commutant, so the different
corners are orthogonal also after applying every commutator.  Set

```text
x_n = beta_n^(-1/2) sum_(j in B_n) x_(n,j).
```

Converting corner-normalized norms to the ambient normalized Hilbert--Schmidt
norm gives exactly

```text
||x_n||_2^2 = beta_n^(-1) sum_(j in B_n) tau_n(p_(n,j)) = 1,

sum_s ||[g_(s,n),x_n]||_2^2 < kappa^2/4.
```

Moreover `x_n` is orthogonal to `A_n`.  Indeed, for `a in A_n`, all
cross-corner terms have zero trace, while
`p_(n,j) A_n p_(n,j) = C p_(n,j)` by minimality and the diagonal term has
zero corner trace.  Thus

```text
< x_n, a >_(L2(M_(d_n))) = 0  for every a in A_n.
```

Pass to the Hilbert-space ultraproduct of the `L2(M_(d_n))`.  The classes of
the `g_(s,n)` give the genuine conjugation representation `Ad pi` of
`Gamma`.  Let `x=[x_n]_omega`.  Then `||x||_2=1` and its Kazhdan energy is
strictly below `kappa^2/4`.

The fixed-vector space of `Ad pi` is `L2(N)`, where
`N=pi(Gamma)' cap M_omega`.  By the centralizer-capture hypothesis every
bounded element of `N` has a representative in `prod_omega A_n`; hence the
coordinatewise orthogonality above makes `x` orthogonal to `N`, and therefore
to its `L2`-closure `L2(N)`.  The Kazhdan inequality now gives

```text
sum_s ||Ad(pi(s))x-x||_2^2 >= kappa^2 ||x||_2^2 = kappa^2,
```

contradicting the upper bound `kappa^2/4`.

Thus `beta_n ->_omega 0`.  Keeping the complementary minimal projections
gives the asserted gap.  The argument also explains the correct finite-level
objects.  A central projection of `A_n` is an isotypic block and may have a
matrix multiplicity algebra inside its corner, so its adjoint fixed space can
be much larger than the scalars.  A minimal projection `p in A_n` instead has
`p A_n p = C p`, exactly what the scalar Poincare inequality needs.
