---
rg: 2
id: overlap-hecke-coboundaries-have-canonical-finite-matrix-models
kind: claim
title: The full single-overlap Hecke orbit of a trace-zero coboundary has canonical finite matrix models
distinct_from:
  arithmetic-leak-commutator-localizes-in-overlap-commutant: that proves every arithmetic leak lands in the finite-index overlap commutant; this proves that the resulting overlap, coboundary, and Hecke-orbit data have exact finite matrix countermodels and therefore cannot finish transfer.
  finite-spherical-moments-do-not-fold-regular-double: that realizes finitely many spherical moments by abstract diagonal quadrature without extending them to a group action; this realizes the entire quasi-regular orbit Gram kernel by exact unitaries covariant under an exact asymptotically regular lattice representation.
  sl3-one-parahoric-multiplicity-flow-has-a-tracezero-gauge: that inserts a free spectator into one given transport packet; this gives a canonical lattice sequence and an explicit finite Bernoulli model for every conjugate of the overlap-central coboundary at once.
---

Let `Lambda` be finitely generated and residually finite, and let
`M<Lambda` have finite index `q>=2`.  There are exact finite-dimensional
representations `pi_j:Lambda->U(d_j)` with canonical limiting character and
unitaries `U_j,H_j,W_j` such that

```text
[U_j,pi_j(Lambda)]=1,
W_j=[U_j,H_j],
[W_j,pi_j(M)]=1,
tr(W_j)=0,                                               (OHC1)
```

and, for all `g,g' in Lambda`,

```text
tr( Ad(pi_j(g))(W_j)^* Ad(pi_j(g'))(W_j) )
 = 1_M(g^(-1)g').                                      (OHC2)
```

Thus the conjugacy orbit of `W_j` is an exact isometric copy of the
quasi-regular basis of `ell^2(Lambda/M)`.  Every single-overlap Hecke-walk
Gram moment, including every iterate of a finite coset average, is already
realized in finite matrices; no limiting quadrature is needed.

Apply this to

```text
Lambda=SL_3(Z),
M=Lambda cap h Lambda h^(-1).
```

The output has all conclusions of
`arithmetic-leak-commutator-localizes-in-overlap-commutant`, exact
coboundary form, and canonical lattice trace, while retaining maximal
nonscalar mass.  Therefore no argument based only on the finite-index
decomposition of `pi_j(M)'`, the `Lambda/M` Hecke orbit, positivity of its
Gram matrices, or the fact that `W_j` is a commutator can prove projective
transfer.

The construction deliberately does **not** extend `H_j` to an approximate
image of the denominator generator in `SL_3(Z[1/2])`.  This precisely fences
it from the regular-HNN leak: the HNN leak satisfies all ambient relations
but lives in a possibly non-CE tracial algebra, whereas `(OHC1)--(OHC2)` live
in matrices but omit the ambient denominator relations.  The desired proof
must use both properties simultaneously.  In particular it must couple at
least two arithmetic denominator/Weyl incidences or establish inner-adjoint
correction; one-overlap Hecke decomposition is exhausted.

