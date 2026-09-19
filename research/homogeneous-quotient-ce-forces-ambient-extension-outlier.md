---
rg: 2
id: homogeneous-quotient-ce-forces-ambient-extension-outlier
kind: claim
title: Every embeddable SL3 homogeneous quotient is carried by ambient-extension outliers
distinct_from:
  homogeneous-quotient-ce-forces-sl3-outlier-at-large-primes: that uses the large-prime depth-free theorem to force flexible distance from every genuine lattice representation; this holds at every prime and forces same-dimensional distance only from restrictions of genuine ambient representations.
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that constructs the explicit spherical leak and records the conditional refutation of collapse; this identifies the finite-dimensional representation-theoretic sector in which every matrix realization of that leak must live.
  unbalanced-torus-extracts-near-central-denominator-coordinate: that closes the ambient-extendable sector for an arbitrary projective-transfer enemy; this applies it to the compact homogeneous-quotient crossed product.
---

Fix a prime `p`, put

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),
```

and let `Lambda' < SL_3(Q_p)` be a torsion-free cocompact lattice for
which `X=SL_3(Q_p)/Lambda'` has at least two `SL_3(Z_p)`-orbits.  Put

```text
M_p=L^infinity(X) rtimes A.
```

If `M_p` is Connes embeddable and

```text
theta:M_p -> prod_U M_(d_n)
```

is any trace-preserving embedding, then every representing microstate
sequence `(X_n,H_n)` for the canonical copy of `A` satisfies, for a fixed
finite generating set `S` of `C`,

```text
liminf_(n->U) inf_(sigma:A->U(d_n))
  max_(s in S)||X_(n,s)-sigma(s)||_2 > 0.              (HQO1)
```

Thus every matrix realization of this explicit spherical leak is an
**ambient-extension outlier**: its lattice coordinates remain uniformly
far from the restriction of every exact same-dimensional representation
of the full S-arithmetic actor.

This conclusion holds for every prime.  It is weaker than flexible lattice
outlierness: the latter also excludes compressions of arbitrary genuine
lattice representations after `o(d_n)` padding, and is presently known for
this crossed product only at `p>=11`.  The point of `(HQO1)` is different:
it identifies directly, with no conductor decomposition, the exact residual
sector which an embeddability construction for `M_p` would have to realize.

DERIVATION
homogeneous-quotient-ambient-outlier-proof
