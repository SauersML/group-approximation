---
rg: 2
id: stone-additive-semidir-product-trace-proof
kind: route
title: Restrict the semidirect-product regular trace to the additive event group
target: stone-additive-semidir-product-loses-manzoor-measure
requires:
  - stone-multiplicative-locus-is-haar-null-in-additive-dual
  - manzoor-natural-subgroup-subshift-is-not-a-haar-envelope
---

The action on the measure algebra preserves symmetric difference, so `(SAS1)`
is well defined and countable.  The canonical group trace vanishes on every
nonidentity element of `K`, proving `(SAS2)`.  The labeled-Schreier Bernoulli
coordinate supplies an event of measure `1/3`, so the canonical and desired
traces differ on an explicit generator after adjoining that event and its
countable orbit to `A`.  The null-selector and corner conclusions are the
specialization of
`stone-multiplicative-locus-is-haar-null-in-additive-dual`.

