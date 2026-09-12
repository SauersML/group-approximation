---
rg: 2
id: culf-mastel-rstar-support-audit-proof
kind: route
title: Check non-TVF fibers and inspect the classical extension map in Theorem 6.8
target: culf-mastel-rstar-reduction-is-support-blind
requires:
  - rstar-fano-ghost-affine-hull-criterion
  - culf-mastel-oracular-2csp-perfect-gap-family
---

Every fixed assignment on two coordinates of the odd parity hyperplane has
two completions, so deletion of one ghost leaves one; this proves non-TVF.
The cited proof of Theorem 6.8 uses only the existential restriction property
`(CMS1)` for the NP reduction.  That property controls which source
assignments extend, but places no restriction on the union of target
assignments used by a trace.  The Fano criterion shows that excluding the
ghost after affine closure requires precisely the additional no-line support
condition, which is absent from the cited hypotheses and conclusions.
