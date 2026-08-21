---
rg: 2
id: two-matchings-force-exponential-dimension-with-multiplicity
kind: claim
title: Two primitive field matchings force the complete Weyl table with arbitrary spectral multiplicity
distinct_from:
  two-matchings-force-full-weyl-on-multiplicity-free-spectra: that obtains every character by scalar overlap rectangles; this uses matrix-block bridges and works with arbitrary multiplicities.
  two-field-matchings-rigidify-linear-weyl-mislabels: that treats deterministic linear translations; this treats arbitrary pairs of commuting finite-dimensional actions.
---

Identify `V=F_(2^n)` as an `n`-dimensional binary space with trace pairing

```text
<a,b>=Tr(ab).
```

Let `A` be multiplication by a primitive field element `alpha`; it is
self-adjoint for this pairing.  Let `U,W:V->U(H)` be arbitrary exact unitary
representations, with no restriction on spectral multiplicities.  Suppose
for every `b in V`,

```text
U(b) W(b)       = (-1)^Tr(b^2)       W(b) U(b),
U(alpha b) W(b) = (-1)^Tr(alpha b^2) W(b) U(alpha b).           (PM1)
```

Then

```text
U(a) W(b) = (-1)^Tr(ab) W(b) U(a)       for every a,b in V,     (PM2)
2^n divides dim(H).                                              (PM3)
```

Thus the union of two degree-one mixed matchings is not merely an
unbounded exact Pauli dimension witness: it forces the entire Weyl table
after exact same-basis linearity.  There is no nonlinear commuting-action or
multiplicity-intertwiner countermodel in any dimension.  The earlier
`2^n-1` bridge-orbit bound is strictly superseded by `(PM2)--(PM3)`.

The proof is the canonical-tensor untwisting corollary of
`two-untwisted-field-matchings-force-complete-cross-commutation`: tensor
`U,W` with a canonical Pauli pair so the two sampled signs cancel, apply the
abstract group theorem, and untensor.  The normalized-HS robust version with
a rank-independent constant remains open in
`two-matching-matrix-block-propagation`.
