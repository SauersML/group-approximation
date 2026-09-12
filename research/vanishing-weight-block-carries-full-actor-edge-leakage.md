---
rg: 2
id: vanishing-weight-block-carries-full-actor-edge-leakage
kind: claim
title: A vanishing-weight block carries divergent edge leakage beside the full Kazhdan actor
distinct_from:
  kt-infinite-index-returns-force-divergent-edge-leakage: That derives divergent leakage from the reduced edge expectation for every fixed exterior return; this shows that the resulting unnormalized divergence can be carried entirely by a summand invisible to all normalized group moments, and deliberately fails the exterior-return expectation on the dominant summand.
  kt-full-actor-extension-is-locally-hs-unstable: That extends bad local actor approximations through a central lamp and loses canonical lamp separation; this keeps the canonical actor character and produces a prescribed divergent edge-superoperator leakage, but makes no lamp model.
---

Let `Gamma<G` be the explicit Kun--Thom pair and fix a strict compressor
`t in G`.  There are canonical normalized-Hilbert--Schmidt approximate
representations

```text
phi_r:G->U(d_r)
```

of the **full** residually finite Kazhdan actor such that, for

```text
B_r=C*(phi_r(Gamma)),       T_r=phi_r(t),
```

one has

```text
||(1-E_(B_r))Ad(T_r)E_(B_r)||_HS^2 -> infinity.        (VBL1)
```

The maps satisfy every fixed multiplication and strict-compressor word with
normalized-Hilbert--Schmidt defect tending to zero, and their characters
converge to the canonical character of `G`.  Thus neither the full actor
relations, property `(T)`, the presence of the genuine strict compressor,
nor canonical group moments conflict with divergent unnormalized edge
leakage.

The construction is deliberately **not** a reduced relative model.  For a
fixed exterior return `h=t^(-1)gamma t outside Gamma`, its dominant exact
finite-image block is absorbed by the edge algebra, and hence

```text
||E_(B_r)(phi_r(h))||_2 ->1.                            (VBL2)
```

Consequently this does not refute
`kt-infinite-index-returns-force-divergent-edge-leakage` and does not prove
`kt-double-reduced-cstar-is-mf`.  It proves a scope firewall: the divergence
in that theorem is not stable under tracial equivalence and cannot itself be
combined with the full-actor relations to get a contradiction.  A successful
Certificate C obstruction must force the leakage to live on the same
nonvanishing physical-trace sector on which the exterior return expectations
vanish, or replace `(VBL1)` by a normalized/weighted invariant which cannot be
exported to a vanishing summand.

DERIVATION
vanishing-weight-full-actor-leakage-proof
