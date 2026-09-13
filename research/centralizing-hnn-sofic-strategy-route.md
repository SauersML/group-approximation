---
rg: 2
id: centralizing-hnn-sofic-strategy-route
kind: route
title: Free edge action and a perturbed non-quotient model, then a stable letter in the edge centralizer
target: sofic-safe-finite-presentation-compiler
requires:
  - centralizing-hnn-sofic-via-regular-edge-centralizer
  - centralizing-hnn-perturbed-edge-separation
  - mf-safe-finite-presentation-compiler
  - twisted-rope-sofic-once-first-rope-sofic
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
`L_e` of infinite index.  Given the exact centralizer/no-go analysis
[[centralizing-hnn-sofic-via-regular-edge-centralizer]] and the genuinely
missing non-quotient separation theorem
[[centralizing-hnn-perturbed-edge-separation]], `Gamma_e` is sofic.  Its
product with `Q_e` is sofic (direct products of sofic groups
are sofic), and the final rope edge is an HNN extension whose two edge
embeddings become exactly conjugate after tensoring with the synchronizing
finite quotients (the permutation Fell absorption
`Q x Y ~= |Y| copies of the regular Q-set`, recorded in
[[sofic-safe-finite-presentation-compiler]]); the same free-edge argument
applies to that edge because its base is then sofic and the edge subgroup
`S_e` acts with the required freeness in the synchronized models.

On the `FIN` branch nothing is needed: the output contains the nonsofic
seed and fails soficity by heredity.

## Correction (2026-09-13, lane ex3-pfg-second-rope)

This route is already invalidated by
[[final-rope-canonical-tensor-conjugator-is-not-faithful]]. The canonical
product-form conjugator kills the Britton word `[u,(k,1)]`, `k in K_0`.

Separately, the sentence "the same free-edge argument applies to that edge"
is unsupported, and the route never named the final edge as a premise. It is
now a premise: [[twisted-rope-sofic-once-first-rope-sofic]].

1. The free-edge argument picks the stable letter inside the centralizer
   (CE1) of one free edge action. The final letter must instead conjugate two
   different restrictions of the base model to `S_e`, so (CE1) does not
   apply.
2. The synchronized models kill `K_e^0` in their finite factor
   (`research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`,
   Section 3.4). The MF proof recovers injectivity only in the universal HNN
   algebra, and permutation models have no analogue of that step. The
   invalidator above is the concrete form of this failure.
3. Exact conjugacy is available at the group level.
   [[twisted-rope-is-a-central-rope-over-an-rf-envelope]] makes the twist
   inner in `Gamma_e x R-hat`, with `R-hat` a fixed residually finite group,
   and embeds `R_e` in a central rope over an isomorphic copy of `S_e`.
   Britton separation for that edge is a separate problem. It is not
   [[centralizing-hnn-perturbed-edge-separation]], whose edge is `L_e` in
   `K_e`.
