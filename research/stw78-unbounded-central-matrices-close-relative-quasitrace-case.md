---
rg: 2
id: stw78-unbounded-central-matrices-close-relative-quasitrace-case
kind: claim
title: Unbounded central matrix blocks solve LXXVIII when the ordinary relative commutant is quasitraceless
distinct_from:
  stw78-central-matrix-folding-descends-proper-infiniteness: that folds one already matched properly infinite amplification; this theorem obtains a matching amplification from quasitracelessness and unbounded central matrix sizes.
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Let `phi:A->B` be a unital homomorphism.  Assume:

1. for arbitrarily large integers `r`, there is a unital homomorphism
   `M_r->A_infinity intersect A'`;
2. the ordinary relative commutant `B intersect phi(A)'` contains a unital
   C-star subalgebra `C` with no normalized 2-quasitrace.

Then `phi` is O-infinity-stable.

This gives a positive LXXVIII class without nuclearity or exactness of the
target.  It also isolates why quasitracelessness of the whole target is not
yet enough: its finite obstruction seed need not lie in the ordinary
relative commutant.
