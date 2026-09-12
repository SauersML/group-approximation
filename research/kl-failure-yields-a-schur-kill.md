---
rg: 2
id: kl-failure-yields-a-schur-kill
kind: claim
title: Every Kervaire--Laudenbach failure yields a nonzero Schur kernel with the same equation
distinct_from:
  kl-counterexample-absorbs-any-countable-group: that free-multiplies a prescribed group into a counterexample and keeps a coefficient kill; this amalgamates a torus along the killed coefficient and turns the kill into a killed second-homology class.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `G` be countable, `w in G * <t>` nonsingular, and `1 != a in G` dying in
`(G * <t>)/<<w>>`. Put `Q = G *_(<a>) (<a> x Z)`. Then the torus class of
`a` and the generator of `Z` is nonzero in `H_2(Q; Z)`, and it dies in
`H_2((Q * <t>)/<<w>>; Z)`.

Consequently every violating equation gives a nonzero Schur kernel, and Schur
injectivity for all nonsingular adjunctions implies the Kervaire--Laudenbach
conjecture.

DERIVATION
kl-failure-schur-kill-proof
