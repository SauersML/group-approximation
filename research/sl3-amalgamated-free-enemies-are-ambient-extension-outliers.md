---
rg: 2
id: sl3-amalgamated-free-enemies-are-ambient-extension-outliers
kind: claim
title: Every SL3 amalgamated-free HNN enemy is a uniform ambient-extension outlier
distinct_from:
  sl3-hnn-admits-no-amalgamated-free-haar-unitary: that excludes the enemy altogether; this proves only that any enemy is uniformly separated from restrictions of exact same-dimensional ambient representations.
  unbalanced-torus-extracts-near-central-denominator-coordinate: that is the finite-dimensional inequality for an arbitrary projectively lattice-central auxiliary unitary; this inserts the exact subgroup-indicator moment forced by amalgamated freeness and states the resulting reduction for the HNN endpoint.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that confines exact leaks after a lattice correction to the dyadic conductor sector; this shows that the original lattice packet cannot be close to an exact ambient representation at all, independently of any conductor decomposition.
---

Let

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),
```

and let `S` be the fixed lattice generating set used in
`unbalanced-torus-extracts-near-central-denominator-coordinate`.  Suppose
that a trace-preserving embedding `pi:L(A)->M` into a tracial matrix
ultraproduct admits a unitary

```text
k in pi(L(C))' intersect M
```

such that `W^*(pi(L(C)),k)` and `pi(L(A))` are free with amalgamation over
`pi(L(C))`, and `E_(L(C))(k^n)=0` for every nonzero integer `n`.

Represent `pi` by finite-dimensional approximate actors `(X_n,H_n)` and
`k` by unitaries `K_n` of the same dimensions.  Then there is an
`epsilon>0` such that, on an ultrafilter-large set of indices,

```text
inf_(sigma:A->U(d_n)) max_(s in S)||X_(n,s)-sigma(s)||_2 >= epsilon.   (AEO1)
```

The infimum is over exact representations of the whole ambient group in
the same dimension.  Thus every surviving HNN model lies in the
ambient-extension-outlier sector; congruence models, arbitrary direct sums
of exact ambient representations, and all their same-dimensional
multiplicity patterns are excluded.

This does not rule out `(AEO1)`: an approximate representation of the
lattice can be far from the restriction of every exact ambient
representation even when it is close to some exact lattice representation.
That extension gap is the remaining analytic seam.
