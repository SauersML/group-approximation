---
rg: 2
id: two-site-coupling-route-to-a5-classicalization
kind: route
title: Classicalize the marked A5 center through multiplicative block-mass couplings
target: two-site-a5-center-classicalization
requires:
  - two-site-a5-plancherel-center-separates-mark
  - finite-pvm-couplings-with-approximate-inverses-classicalize
  - two-site-center-measurement-interference-is-relator-paid
---

For each finite actor window, use the interference estimate to obtain a
finite family of center block-mass couplings satisfying `(FPC1)`.  The PVM
coupling theorem replaces them by approximately multiplicative finite
permutations.  The center projection at a site becomes a literal binary
label on the replicated atom states; `(TAP4)` gives the required covariance
whenever the actor incidence stays in the marked pair, and `(TAP3)` gives a
fixed positive density of states on which the two labels differ.

Amplify and apply the standard good-set shrinking used in the definition of
two-point approximation.  Tensoring with a free residual-finite actor model,
if needed, makes the actor permutations sofic without changing the labels or
their separation.  This supplies exactly the finite data asserted by
`two-site-a5-center-classicalization`.

