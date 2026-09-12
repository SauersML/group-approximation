---
rg: 2
id: dyadic-affine-pauli-patterns-have-odd-periodizations
kind: claim
title: Every finite dyadic-affine Pauli pattern has an exact odd periodization
distinct_from:
  finite-stencil-pauli-tape-has-marked-periodizations: that periodizes a finite translation stencil on one cyclic shift orbit; this also absorbs the nonlinear Baumslag--Solitar scale conversion by reducing dyadic-rational addresses modulo an odd integer.
  periodic-dyadic-root-clocks-keep-weyl-overlap: that builds one period-four root-spectrum model for a Weyl/coweight packet; this proves a general local-pattern theorem for arbitrary finite Pauli site tables over the dyadic affine action.
  periodic-bs-clock-defeats-spectral-first-hit-checksum: that gives spectral first-hit countermodels for one clock; this preserves all equality, inequality, covariance, same-site Pauli, and off-site commutation data in an arbitrary prescribed finite address pattern.
---

ESTABLISHED.  Let

```text
B=<a,t | t a t^(-1)=a^2>                               (FDA1)
```

act on `X=Z[1/2]` by

```text
a.x=x+1,             t.x=2x.                            (FDA2)
```

Fix any finite set `F subset X`.  There is an odd integer `m` for which the
reduction map

```text
rho_m:F -> Z/mZ,
rho_m(n/2^s)=n 2^(-s) mod m                             (FDA3)
```

is injective.  To see this, write every nonzero difference of two elements
of `F` as `u/2^v` and choose an odd prime `m` dividing none of the finitely
many nonzero numerators `u`.

Let `ell` be the multiplicative order of `2 mod m`.  The finite affine group

```text
A_m=(Z/mZ) rtimes <2>,              |<2>|=ell,           (FDA4)
```

is a quotient of `B`: translation by one is the image of `a`, multiplication
by two is the image of `t`, and `(FDA1)` holds.  Its action on `Z/mZ`
intertwines `(FDA3)` with every affine address operation which occurs among
the elements of `F`.

Now attach one Pauli pair at every point of `Z/mZ`, identify all local
centers with one involution `J`, and let `A_m` permute the sites.  The resulting
finite group is

```text
K_(Z/mZ) rtimes A_m,                                    (FDA5)
```

where distinct sites commute and every same-site pair has commutator `J`.
It has the exact tensor-Pauli representation on `(C^2)^(tensor m)` with
`J=-I`.

Consequently every finite group-word table over the dyadic affine addresses
whose relations use only

```text
affine covariance,
equality or inequality of the finitely many addressed sites,
same-site Pauli relations,
off-site commutation                                      (FDA6)
```

has an exact finite-dimensional marked realization: take `F` to contain all
sites occurring in the table and use `(FDA3)--(FDA5)`.  All declared distinct
sites remain distinct, so no wraparound relation detects the periodization.

Thus adjoining the nonlinear depth rule `t a t^(-1)=a^2` does not make a
finite address table see the extensive terminal seam.  In odd finite models
doubling is invertible and the binary depth geometry folds into a finite
affine permutation orbit with zero relator defect.  A viable full-tree
compiler must impose a relation not determined by any finite affine site
pattern--for example a growing equality/linearity component with uniform
soundness, a trace-cyclic proper-corner relation, or an authenticated
matrix-coordinate square function.
