---
rg: 2
id: centralizing-hnn-sofic-strategy-route
kind: route
title: Free edge action and a perturbed non-quotient model, then a stable letter in the edge centralizer
target: sofic-safe-finite-presentation-compiler
requires:
  - centralizing-hnn-sofic-via-regular-edge-centralizer
  - mf-safe-finite-presentation-compiler
---

## Status

The quotient-model version of this route is **refuted** in
[[centralizing-hnn-sofic-via-regular-edge-centralizer]]: closure points of
the edge kill the pinches at every scale.  What the route still asks for is
the perturbed version --- an approximate model of `K_e` keeping `L_e`
acting freely while separating `cl(L_e) \ L_e` --- together with the
separation lemma.  The route is kept because the second half (the final
rope edge) is unaffected.

## Why sufficient

The compiler's first rope is `Gamma_e = <K_e, v | [v, L_e] = 1>` with
`K_e` a finite direct product of free groups, hence residually finite, and
`L_e` of infinite index.  Given
[[centralizing-hnn-sofic-via-regular-edge-centralizer]], `Gamma_e` is
sofic.  Its product with `Q_e` is sofic (direct products of sofic groups
are sofic), and the final rope edge is an HNN extension whose two edge
embeddings become exactly conjugate after tensoring with the synchronizing
finite quotients (the permutation Fell absorption
`Q x Y ~= |Y| copies of the regular Q-set`, recorded in
[[sofic-safe-finite-presentation-compiler]]); the same free-edge argument
applies to that edge because its base is then sofic and the edge subgroup
`S_e` acts with the required freeness in the synchronized models.

On the `FIN` branch nothing is needed: the output contains the nonsofic
seed and fails soficity by heredity.
