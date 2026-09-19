---
rg: 2
id: cmps-lemma20-primary-source-proof
kind: route
title: Read the radius-two quantifier in CMPS Lemma 20 and its use in Theorem 19
target: cmps-lemma20-is-radius-two-incidence-commutation
requires: []
---

Lemma 20(2) says that observables in one source context commute.  Lemma
20(3) says verbatim that `[A_x,A_y]=0` whenever there are contexts `i,j` and
a variable `z` with `x,z in V_i` and `y,z in V_j`.  This is precisely
`(C2O1)--(C2O2)` and, with `z` fixed, applies to every pair in the union of
the incident contexts.

The proof of Theorem 19 confirms that the quantifier is not shorthand for
sampled-edge commutation: it applies Lemma 20(2)--(3) to commute two answer
PVMs whenever their smooth-label-cover questions have a possible common
partner.  Functional calculus passes commutation of the binary observables
to their spectral projections; products and linear combinations then pass
it to the finite context algebras.  Their mutually commuting atomic PVMs
have the usual product joint refinement.

The citation makes only an existential completeness assertion, so the claim
deliberately records one chosen value-one model rather than all perfect
models.
