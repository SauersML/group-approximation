---
rg: 2
id: central-extensions-of-torsion-free-kl-proof
kind: route
title: The Schur kernel over the torsion-free quotient vanishes, so the central criterion injects the extension
target: kl-holds-over-central-extensions-of-torsion-free-groups
requires: [amenable-t-shape-adjunctions-kill-no-schur-class, central-extension-kl-schur-criterion]
artifacts:
  - research/artifacts/kl-torsion-free-asphericity-pins-2026-09-13.md
---

`deg_t(w-) = deg_t(w) != 0`, so `w-` is nonsingular. Its coefficients lie in
the torsion-free group `Q` itself, and its reduced `t`-shape is amenable.

1. `amenable-t-shape-adjunctions-kill-no-schur-class`, with `B = Q`, gives that
   `Q -> (Q * <t>)/<<w->>` is injective and that `K_2(Q, w-) = 0`.
2. Let `alpha` be the class of the extension. Then
   `alpha_H(K_2(Q, w-)) = alpha_H(0) = 0`.
3. Part 1 of `central-extension-kl-schur-criterion` has two hypotheses:
   injectivity of `Q -> (Q * <t>)/<<w->>`, and the vanishing in step 2. It
   concludes that `E -> (E * <t>)/<<w>>` is injective.

For the corollary, apply this with `Z = T`, the central subgroup of
finite-order elements. When `deg_t(w) = ±1`, every shape of exponent sum `±1`
is amenable, so no reduction condition is left to check.
