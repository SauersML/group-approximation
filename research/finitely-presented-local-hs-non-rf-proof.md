---
rg: 2
id: finitely-presented-local-hs-non-rf-proof
kind: route
title: Derive the finitely presented local-HS non-RF statement from its recorded inputs
target: finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear
requires:
  - hyperlinear-hs-stable-is-residually-finite
  - hs-stability-plus-fd-residual-forces-nonhyperlinearity
---

Apply Fournier-Facio--Gerasimova--Spaas,
arXiv:2307.13155v2, Lemma 3.11: for a finitely presented group, local and
global stability coincide for any sequence of metric groups, and likewise
for the flexible variants.  Specialize to unitary groups with normalized
Hilbert--Schmidt distance.  The resulting global HS stability and assumed
hyperlinearity imply residual finiteness by
`hyperlinear-hs-stable-is-residually-finite`, contradicting the hypothesis.
For a flexible variant, choose a nontrivial word in the finite residual and
apply `hs-stability-plus-fd-residual-forces-nonhyperlinearity` after the same
local-to-global upgrade; the `o(d)` padding does not affect separation of the
fixed word.

For the literature boundary, combine the same lemma with the abstract's
statement that the paper's non-RF examples are locally HS-stable but not
HS-stable: those examples cannot be finitely presented.
