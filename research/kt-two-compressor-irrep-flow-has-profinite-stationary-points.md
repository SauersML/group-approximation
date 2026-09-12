---
rg: 2
id: kt-two-compressor-irrep-flow-has-profinite-stationary-points
kind: claim
title: The two Kun--Thom compressor flows have canonical profinite stationary irrep distributions
distinct_from:
  kt-kazhdan-polar-compressor-rounding-is-directional: That identifies the unmatched-support obstruction for one partial compressor intertwiner; this proves that adding the second compressor still gives no scalar boundary gap on the weighted Gamma-irrep multiset.
  kt-two-positive-compressors-generate-full-obstruction: That proves two compressors already obstruct common permutation coset models; this shows why the obstruction is invisible after forgetting the lamp multiplicity algebra and retaining only actor irrep weights.
  kt-single-root-mixed-return-has-exact-finite-countermodels: That retains a separated two-lamp pair with only one root stabilizer; this constructs stationary actor type flows for the full Gamma packet but does not retain the marked lamp separation.
---

**ESTABLISHED.**  Let `A,B` be the two positive compressors of
`kt-two-positive-compressors-generate-full-obstruction`.  For every finite
actor window `F subset G` there is an exact finite-dimensional representation
`pi` of `Gamma` whose normalized character is canonical on `F intersect
Gamma` and whose dimension-weighted irreducible multiplicity distribution is
simultaneously stationary under precomposition by `alpha_A` and `alpha_B`.

More explicitly, residual finiteness gives a finite quotient `q:G->K`
separating all nonidentity elements of `F`.  Put `S=q(Gamma)`.  Compression
and finite cardinality give

```text
q(A)S q(A)^(-1)=S=q(B)S q(B)^(-1).                    (KTF1)
```

For `pi=lambda_S after q|Gamma`, both `pi after alpha_A` and
`pi after alpha_B` are unitarily equivalent to `pi`.  In irreducible
coordinates its physical weight is the Plancherel vector

```text
mu(tau)=dim(tau)^2/|S|,                                (KTF2)
```

and each compressor merely permutes this vector.  Hence every proposed
dimension-uniform inequality of the form

```text
boundary_A(mu)+boundary_B(mu) >= c>0                  (KTF3)
```

from canonical actor traces and the two partial-intertwiner flows is false.

There is a second, independent loss in passing to `mu`.  For a general
finite-dimensional `Gamma` representation, an irreducible `tau` need not
remain irreducible after precomposition by a proper compressor; the flow is a
branching multiplicity operator, not a map on irreducible types.  More
importantly, the rounded base lamp lies in `pi(Gamma)'`, which is precisely
the matrix algebra on the isotypic multiplicities.  The scalar vector `mu`
forgets the compressor action on this algebra.  In the finite quotient models
the full stabilizer packet makes the mixed return collapse because its image
lies in `S`; the canonical wreath demands the opposite lamp separation.
That conflict cannot be expressed by `(KTF2)`.

Therefore the surviving two-compressor theorem must be
**projection-valued and multiplicity-sensitive**: it must charge the
compressor action on a specified projection in `pi(Gamma)'`, jointly with the
mixed-return lamp trace.  A free-semigroup boundary estimate on the weighted
irrep multiset alone cannot prove the unitary-HS floor.

DERIVATION
kt-two-compressor-profinite-type-flow-proof
