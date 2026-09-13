---
rg: 2
id: euler-class-protection-fails-for-o2-self-similar-modules-proof
kind: route
title: Proof that O_2 self-similarity forces trivial summands that kill the Euler class
target: euler-class-protection-fails-for-o2-self-similar-modules
requires: []
artifacts:
  - research/artifacts/lxi-o2-multiplier-reduction-2026-09-12.md
---

Artifact, Proposition 5.

1. `E ≅ E ⊕ E` gives isometries `S_1, S_2 ∈ L(E)` with orthogonal ranges summing to 1. If `ξ` is a
   unit section, the four sections `S_iS_jξ` are orthonormal.
2. The projections onto `E_n` converge strictly to 1. Compress the four sections to a late `E_n`: their
   Gram matrix is within `1/2` of the identity, and Gram--Schmidt with continuous coefficients gives four
   orthonormal sections of `E_n`. So `E_n ≅ θ^4 ⊕ η` with `η` projective of rank `r_n + 2 - 4`.
3. By the Whitney sum formula, `c(P_n) = c(θ^2 ⊕ P_n) = c(E_n) = c(η)`. Since `rank η < r_n`, the
   component `c_{r_n}(η)` is zero. So `e(P_n) = c_{r_n}(P_n) = 0`.
