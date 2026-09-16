---
rg: 2
id: morphic-sft-matricial-iff-scale-one-torus-module
kind: claim
title: For a free minimal Z^2-SFT carrying a 2-dimensional self-morphism of its language with all letter images at least 2 by 2, exact matriciality over a finite field holds iff one scale-1 torus tiling algebra has a nonzero finite-dimensional module
distinct_from:
  self-similar-sft-matricial-iff-one-torus-module: that needs a substitution of constant shape and a scale-3 module; this allows letter-dependent shapes (as in Labbé's morphism) and needs only a scale-1 module
  torus-quantum-tilings-decide-matriciality-of-sft-rings: that needs torus modules at every scale for every free minimal SFT; this reduces to one scale-1 module when a shape-consistent self-morphism exists
  morphism-towers-double-covariant-tiling-scales: that is the family-level inflation step; this combines it with the torus criterion and descent into a one-scale decision
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be a free minimal SFT, `k` a finite field, and `ω` a 2-dimensional
morphism on `L(Ω)` with `ω(L(Ω)) ⊆ L(Ω)` and every letter image of shape `>= (2,2)`. Then `LC(Ω,k) ⋊ Z^2` embeds
unitally in an algebraic ultraproduct of matrix algebras over fields iff, for some finite-index `Λ ≤ Z^2`, the torus
tiling algebra `𝒯_(1,Λ)(Ω,k)` has a nonzero finite-dimensional module.

**Remarks.**
- No recognizability, primitivity or ontoness of `ω` is used.
- Scale `1` means the relations use only the global `B_1`-language (legal `3×3` patches) and commutation within
  sup-distance `2`.
- The existence of such a module depends only on the characteristic `p` of `k`. The relations have coefficients
  `0, 1`, so modules extend along `F_q ⊆ F_(q^m)` and restrict back.

Route: `morphic-sft-matricial-iff-scale-one-torus-module-proof` (artifact §6, Theorem B).
