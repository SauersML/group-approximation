---
rg: 2
id: private-random-generator-columns-form-affine-rank-condenser
kind: claim
title: Private random generator columns form a constant-distance affine rank condenser
artifacts:
  - research/artifacts/rank-metric-covering-radius-audit-2026-08-22.md
distinct_from:
  degree-one-generator-columns-have-sqrt-minrank-but-no-gap: that forces a triangular block but its syndrome is approximated by bounded-rank block matrices; this gives constant relative distance from every rank-o(sqrt(N)) bilinear form.
  sparse-generator-column-sampling-has-bilinear-kernel: that proves sparse sampling cannot recover the full bilinear table exactly; this only forces distance from low-rank completions and permits undetected high-rank twists.
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that controls arbitrary matrix-valued strategies using the complete product distribution; this proves the robust statement only for exact scalar-Weyl bilinear models.
---

For infinitely many ambient dimensions `N`, there are two uniformly
spectrally generating column multisets of length `Theta(N)` and a sampled
bipartite occurrence graph of maximum degree one with the following property.
Writing `r=floor(sqrt(N))`, every bilinear form `B` of rank at most `r/4`
disagrees with the ideal dot-product signs on at least one quarter of the
sampled edges:

```text
Pr_(t in E)[a_t^T B b_t != a_t.b_t] >= 1/4.              (PRC1)
```

Consequently every exact scalar-Weyl strategy of sampled sign loss below
`1/4` has carrier dimension at least

```text
2^(r/4)=2^Omega(sqrt(N)).                                 (PRC2)
```

The construction is probabilistic and uses only private matched occurrences.
Take an active `r`-dimensional coordinate subspace and choose

```text
m=64 r^2
```

independent uniform pairs `(a_t,b_t)` in that subspace.  Regard every sample
as a distinct left and right column occurrence and join only its matched pair.
Append these columns to any asymptotically good dimension-`N` generator
matrix on each side.  The base block preserves a constant spectral gap after
the `Theta(N)`-length appendage.

This establishes the exact constant-distance affine-rank-condenser requested
by `bounded-incidence-generator-column-minrank-witness`.  It also shows that
ordinary high girth is compatible with rank soundness: the mixed occurrence
graph is a matching.  The load-bearing input is the dense linear content of
the private column labels, not graph expansion.

The full normalized-HS theorem remains open.  An arbitrary pair of exact
additive unitary representations need not have scalar cross commutators and
therefore need not be described by one bilinear matrix `B`.  The complete
de la Salle product test removes this freedom before Gowers--Hatami
exactification; `(PRC1)` alone only excludes low-rank **scalar Weyl** models.
A terminal proof must promote small sampled HS defect to a scalar/finite-rank
bilinear description, or produce a matrix-valued escape.

Standard rank-metric covering radius does not perform that promotion.  It
measures `min_(C in ker T_E) rank(X-C)` inside a matrix coset, whereas `(PRC1)`
measures Hamming distance of the sparse syndrome from the image of the
bounded-rank variety.  The two metrics and quantifiers are different, as
recorded in the attached primary-source audit.
