---
rg: 2
id: kt-mf-models-have-a-universal-trace-blind-word
kind: claim
title: A nonidentity double word is invisible in every matrix-induced trace
distinct_from:
  weak-mf-embedding-not-reusable: That exhibits individual trace-blind realizations of possibly hyperlinear groups; this gives one nonidentity word invisible in every realization of a fixed MF nonhyperlinear group.
  shulman-presentation-double-has-a-faithful-fold-trace-model: That constructs one fold-trace model; this excludes all matrix-induced traces seeing a suitable word of the Kun-Thom double.
artifacts:
  - research/artifacts/mf-nonhyperlinear-double-separation-2026-09-20.md
---

For each binary Kun-Thom double D with r,d>=3 there is w!=1 such that
every homomorphism from D to a tracial matrix-ultraproduct unitary group
kills w. Consequently, for every operator-norm asymptotic representation
phi_n of D on exhausting windows,

```
||phi_n(w)-1||_(2,norm) -> 0,
tr(phi_n(w)) -> 1.
```

This includes every faithful operator-norm MF realization of D, which
exists. If A is an MF C-star algebra and i:D->U(A) is injective, then
no MF trace on A separates i(w) from 1: every such trace tau has
tau((i(w)-1)^*(i(w)-1))=0. In particular A admits no faithful MF trace.
This does not exclude arbitrary tracial states on A, and supplies no
explicit rate of convergence or displayed word length.

The result inherits Jihao Liu's internality and Andreas Thom's
normalization input through the nonhyperlinear-double premise.
