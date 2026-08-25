---
rg: 2
id: identity-baseline-s3-recurrence-audit-proof
kind: route
title: Separate the local two-child trace identity from successor-prefix incidence
target: identity-baseline-does-not-install-tagged-s3-survivor
requires:
  - two-bit-tag-routing-splits-s3-exit-and-survivor
  - companion-free-prefix-return-has-exponential-regular-capacity
---

The endpoint and tag projections give `(IBS1)--(IBS2)`, and trace
additivity gives `(IBS3)`.  If the identity summand is the same carrier, its
exit subprojection is retained.  If it is a separate child, only the routed
live summand is known to lie below the next prefix.  Adding an exact
trace-neutral chart containment for the separate child invokes the
companion-free prefix theorem and gives `(IBS5)`.  These alternatives prove
the stated scope no-go.
