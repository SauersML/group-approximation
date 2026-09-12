---
rg: 2
id: centralizer-capture-controls-nonspiky-gap-failures-proof
kind: route
title: Aggregate bounded bad-corner witnesses inside the tracial ultraproduct
target: centralizer-capture-controls-nonspiky-gap-failures
requires: []
---

Let `beta_n` be the total trace of the `C`-bad minimal blocks.  If the
conclusion fails, restrict to an ultrafilter-large set on which
`beta_n >= eta>0`.  Choose one witness `x_(n,j)` on every bad block and set

```text
x_n = beta_n^(-1/2) sum_(j bad) x_(n,j).
```

Different minimal corners are orthogonal and every `p_(n,j)` commutes with the
generator lifts, so exactly as in the naive aggregation argument,

```text
||x_n||_2=1,
sum_s ||[g_(s,n),x_n]||_2^2 < kappa^2/4.
```

The new hypothesis is what makes the argument legitimate in the tracial
algebra ultraproduct:

```text
||x_n||_op
 <= beta_n^(-1/2) max_j ||x_(n,j)||_op
 <= C/sqrt(eta).
```

Hence `x=[x_n]_omega` is a bounded element of `M_omega`, not merely a vector
in the larger Hilbert-space ultraproduct.

Minimality gives `p_(n,j) A_n p_(n,j)=C p_(n,j)`.  Since each corner witness
has normalized trace zero and cross-corner products have zero trace, `x_n` is
`L2`-orthogonal to `A_n`.  The capture hypothesis therefore makes `x`
orthogonal to

```text
N=pi(Gamma)' cap M_omega=prod_omega A_n.
```

But the commutator energy bound says that the conjugation representation of
`Gamma` on `L2(M_omega)` moves `x` with squared Kazhdan energy below
`kappa^2/4`.  Its fixed space is `L2(N)`, while `x` is orthogonal to that fixed
space and has norm one.  Property `(T)` gives energy at least `kappa^2`, a
contradiction.

The proof fails without the `L^infinity/L^2` bound precisely because
`beta_n^(-1/2) x_(n,j)` may have diverging operator norm and then define only
a Hilbert-ultraproduct vector.  `rank-one-lift-perturbation-gap-no-go` shows
that this is a real obstruction rather than a proof artifact.
