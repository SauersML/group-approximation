---
rg: 2
id: amenable-regular-trace-forces-singular-cover-nonlifting
kind: route
title: Descend the amenable near trace hypothetically and factor the singular state through the Calkin image
target: leavitt-singular-local-lift-iff-no-witness
requires:
  - invariant-free-near-state-is-amenable-regular-cover
  - amenable-trace-descends-through-locally-liftable-quotient
  - openai-leavitt-unit-nonsofic
---

For any hypothetical witness, the upstairs trace is amenable and the
trace-kernel quotient is the reduced group algebra.  A local ucp section would
descend amenability to its regular trace, forcing the Leavitt group to be
amenable and contradicting its established nonsoficity.  Therefore every
actual witness has a nonlocally-split quotient, making the universal positive
local-lift statement equivalent to absence of witnesses.

Pure singularity only adds the factorization `(SLT4)`, since
`A cap K(H) subset I_tau`.  If both arrows there were locally split, their
local sections would compose, contradicting nonlifting of the composite.
Known finite-dimensional nonlifting systems in the Calkin algebra confirm
that the first arrow has no automatic lifting mechanism.
