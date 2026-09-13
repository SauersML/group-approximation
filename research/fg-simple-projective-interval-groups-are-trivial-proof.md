---
rg: 2
id: fg-simple-projective-interval-groups-are-trivial-proof
kind: route
title: The right germ at the first moved point maps a finitely generated piecewise-projective interval group onto a nontrivial metabelian group
target: fg-simple-projective-interval-groups-are-trivial
requires: []
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part1.md
---

## Why sufficient

Full proof in the artifact, Section 3. Let `G = <S> ≤ PP_+(I)`, `S` finite, `G ≠ 1`,
and `c = inf ⋃_(s ∈ S) supp(s)`.

1. **`c` is fixed.** Each generator fixes the points below `c`, so `G` fixes them
   and, by continuity, `c`.
2. **Germ homomorphism.** Each `g ∈ G` agrees on some `[c, c + ε)` with a unique
   projective map `P_g` fixing `c`. Since each `h ∈ G` is increasing and fixes `c`,
   `P_(gh) = P_g P_h`.
3. **Metabelian target.** Conjugating `c` to `∞`, the projective maps fixing `c`
   become the affine maps `x -> λx + μ`, `λ > 0`, whose commutators are translations.
4. **Nontrivial image.** Some generator moves points in every `(c, c + ε)`, so its
   germ is not the identity.
5. **Simple case.** If `G` is simple, `ker ∂ = 1`, so `G` is metabelian and simple,
   hence cyclic of prime order. `PP_+(I)` is torsion-free, because a nontrivial
   increasing homeomorphism has a strictly monotone orbit. So `G = 1`, a contradiction.
