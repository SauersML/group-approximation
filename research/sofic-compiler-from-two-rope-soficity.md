---
rg: 2
id: sofic-compiler-from-two-rope-soficity
kind: route
title: Seed the fixed positive rope with a finitely presented nonsofic group, then make both ropes sofic on INF
target: sofic-safe-finite-presentation-compiler
requires:
  - finite-presentation-rice-criterion-via-the-fixed-positive-rope
  - finitely-presented-nonsofic-group-exists
  - centralizing-hnn-perturbed-edge-separation
  - twisted-rope-sofic-once-first-rope-sofic
---

## Why sufficient

1. **The compiler.** The compiler of
   [[finite-presentation-rice-criterion-via-the-fixed-positive-rope]] is
   uniform in its finitely presented seed `D` (RC1). Take `D` to be the group
   of [[finitely-presented-nonsofic-group-exists]]. On `FIN`, `D` embeds in the
   output. On `INF`, the output is the twisted rope `R_e`.
2. **The first rope.** For `e in INF`,
   [[centralizing-hnn-perturbed-edge-separation]] gives permutation models of
   `Gamma_e = < K_e, v | [v, L_e] = 1 >`. They are multiplicative on balls, and
   every nontrivial Britton word moves a fixed positive fraction of points.
   Amplification (Elek--Szabó) turns this into soficity of `Gamma_e`.
3. **The second rope.** [[twisted-rope-sofic-once-first-rope-sofic]] carries
   soficity from `Gamma_e` to `R_e`.

So on `INF` the output is sofic, and on `FIN` it contains the nonsofic seed.
That is the compiler.

## Scope

This replaces the invalidated
[[centralizing-hnn-sofic-strategy-route]]. It names the final edge as its own
premise, and commits to no particular form for the final stable letter. By
[[final-rope-canonical-tensor-conjugator-is-not-faithful]], a product-form
letter cannot work.
