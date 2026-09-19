---
rg: 2
id: z2-aperiodic-seam-microstate-proof
kind: route
title: Wrap one valid plane tiling on tori and isolate the expander-plus-Cartan hypotheses
target: strong-aperiodic-z2-addresses-have-vanishing-hs-seams
requires:
  - one-dimensional-address-rules-have-periodic-models
  - kun-thom-compression-survives-amenable-near-model
  - simple-lamp-gauge-rigidity-reduces-to-actor-classicalization
---

Copy a valid infinite configuration onto an `N by N` fundamental square and
wrap it to the torus.  Only the `R`-neighborhood of the two seams can violate
a radius-`R` rule, proving `(ZSA1)`.  Diagonal color projections and the two
permutation shifts give `(ZSA2)--(ZSA3)` by the identity
`||P||_2^2=tr(P)` for projections.

For the positive conditional statement, `(ZSA5)` turns an active unitary
model into a finite labeled actor set with controlled loss.  The robust
finite-action bound `(ZSA4)` then charges at least `delta dim(F)` diagonal
atoms, and the fixed word-to-projection estimate gives `(ZSA6)`.  The cited
Kun--Thom and simple-lamp audits show that actor property `(T)`, canonical
moments, and compression alone stop before `(ZSA5)`.
