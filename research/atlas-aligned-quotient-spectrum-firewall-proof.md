---
rg: 2
id: atlas-aligned-quotient-spectrum-firewall-proof
kind: route
title: Quotient the multiplicity tensor and apply the 19243 distance wall
target: atlas-aligned-quotient-spectrum-cannot-reach-low-defect
requires:
  - atlas-aligned-word-jacobian-has-full-multiplicity-absorber
  - atlas-full-relator-data-factor-through-double-commutant-gauge
  - atlas-19243-centrality-forces-s3-distance
---

By `(AJM1)`, the aligned derivative on each rectangular Wedderburn summand is

```text
D_F^(tau,sigma) tensor I_(Hom(M_sigma,M_tau)).        (AQS3)
```

The infinitesimal double-commutant orbit is an invariant subspace of its
kernel.  Passing to the orthogonal quotient removes that subspace but does
not create new singular values: every remaining nonzero singular value is a
singular value of one of the finitely many matrices
`D_F^(tau,sigma)`, repeated with multiplicity
`dim Hom(M_sigma,M_tau)`.  There are only fourteen irreducible labels on
each side, so the set of positive values is finite and independent of `k`.

For the geometric exclusion, an aligned frame identifies the labelled copy
of `K_19243` and therefore lies in its commutant orbit after the fixed chart
transport.  The double-commutant aligned orbit is a subset of `C_K`.
Apply `(19243-DIST)` to obtain `(AQS1)`.  The packet form follows from the
fixed normal-closure estimate for `c_19243`; taking the limit gives `(AQS2)`.
Every fixed tubular neighborhood of the aligned quotient of radius smaller
than `sqrt(2)/16` is therefore eventually disjoint from a low-defect
sequence.  This proves the claimed local-quotient firewall.

