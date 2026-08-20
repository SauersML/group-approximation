---
rg: 2
id: car-substitution-invariant-trace-fence-proof
kind: route
title: Apply marked-trace averaging, and use uniqueness for the CAR algebra
target: car-substitution-invariant-trace-emptiness-is-impossible
requires:
  - sign-preserving-endomorphism-has-invariant-marked-trace
---

Apply `sign-preserving-endomorphism-has-invariant-marked-trace` to the
sign-sector algebra.  This already contradicts `(CIT1)`.  In the CAR case,
if `tau_CAR` is the unique trace, then `tau_CAR after alpha` is another trace,
so uniqueness gives invariance without averaging.  This argument does not
rule out a finite-dimensional anomaly; it rules out the stated
invariant-trace-emptiness mechanism.

