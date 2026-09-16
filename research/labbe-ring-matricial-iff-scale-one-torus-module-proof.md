---
rg: 2
id: labbe-ring-matricial-iff-scale-one-torus-module-proof
kind: route
title: Labbé's morphism squared is a shape-consistent language morphism of Omega_U with all images at least 2 by 2, so the one-scale theorem applies
target: labbe-ring-matricial-iff-scale-one-torus-module
requires:
  - morphic-sft-matricial-iff-scale-one-torus-module
  - labbe-substitution-is-primitive-and-recognizable
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
  - experiments/labbe-covariant-tower-inflation-2026-09-16/omega_shapes.py
  - experiments/labbe-covariant-tower-inflation-2026-09-16/output.txt
---

Artifact §6, Theorem C, and §7.

1. `minimal-aperiodic-wang-shift-exists`: `Ω_U` is a free minimal nearest-neighbour SFT (`r = 1`).
2. `labbe-substitution-is-primitive-and-recognizable`, items 1 and 3: `ω = αβγ : Ω_U -> Ω_U` is a 2-dimensional
   morphism with letter images of shape `<= (2,2)`. Labbé's definition (l.814–823) and his remark "By definition of
   $\omega$, we have $\omega(\L_X)\subseteq\L_Y$" (l.985) give a morphism on `L(Ω_U)` mapping `L(Ω_U)` into itself.
   Independent exact check (script, checks 1, 2, 5):
   - all 19 images are valid Wang patches;
   - widths agree on all 79 colour-matching vertical dominoes, and heights on all 46 horizontal ones;
   - all seams of domino images match.

   So the blockwise image of a valid tiling is valid, and `ω` of a legal word is legal.
3. Composite: for `u`, `v`, `u ⊙^i v ∈ L`, the images are in `L`, and `ω^2(u ⊙^i v) = ω^2(u) ⊙^i ω^2(v)`. So `ω^2`
   is a 2-dimensional morphism on `L(Ω_U)` with `ω^2(L) ⊆ L`.
4. Shapes: the script's check 4 computes `ω^2(a)` for all 19 letters exactly: minimum width `2`, minimum height `2`.
   Import-only alternative: `M^7 > 0` (item 2) and a `(2,2)` letter (item 1) give `shape(ω^8(a)) >= (2,2)`.
5. Apply `morphic-sft-matricial-iff-scale-one-torus-module` to `(Ω_U, F_q, ω^2)`. ∎
