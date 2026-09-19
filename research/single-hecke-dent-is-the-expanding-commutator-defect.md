---
rg: 2
id: single-hecke-dent-is-the-expanding-commutator-defect
kind: claim
title: The one-step Hecke norm dent is quantitatively equivalent to the expanding commutator defect
artifacts:
  - research/single-hecke-dent-commutator-identity-proof.md
distinct_from:
  single-hecke-average-isometry-for-lambda-central-unitaries: that is the open matrix-origin assertion that the dent vanishes; this is an unconditional finite-tracial identity which sandwiches that dent by the single expanding-generator commutator defect.
  one-commutator-controls-distance-to-full-commutant: that uses property (T) to lower-bound the expanding commutator by distance to the full commutant; this compares the expanding commutator directly with one application of the lazy Hecke average and uses no spectral gap.
  balanced-leak-saturates-weighted-rayleigh-tests: that fixes one Rayleigh coefficient while leaving the cross-Gram norm undetermined; this does not determine the norm either, but proves that arbitrary cross-Gram coherence cannot make its dent negligible at fixed expanding commutator defect.
---

Use the notation of
`single-hecke-average-isometry-for-lambda-central-unitaries`, but let
`(M,tau)` be any finite tracial von Neumann algebra and
`pi:Gamma->U(M)` any representation.  Let `xi in L^2(M)` be exactly
`Lambda`-central and put

```text
d=||Ad pi(h)(xi)-xi||_2,
T=(1/L) sum_(i=1)^L Ad pi(w_i),
S=(I+T)/2.
```

Then the following exact identity holds:

```text
||xi||_2^2-||S(xi)||_2^2
  = (1/2)d^2-||S(xi)-xi||_2^2.                         (SHD1)
```

Consequently,

```text
(1/4)d^2 <= ||xi||_2^2-||S(xi)||_2^2 <= (1/2)d^2.     (SHD2)
```

In particular, for a `Lambda`-central unitary `k`,

```text
||S(k)||_2=1  iff  [k,pi(h)]=0.                        (SHD3)
```

Thus the finite cross-Gram matrix of the `L` Hecke translates can change the
size of the one-step dent by at most a factor of two.  It cannot hide a fixed
`h`-commutator behind coherent off-diagonal overlaps.  At the same time,
`(SHD2)` does not force `d=0`; proving that in regular-trace matrix
ultraproducts remains exactly the open matrix-origin content of `(SH1)`.

DERIVATION
single-hecke-dent-commutator-identity-proof
