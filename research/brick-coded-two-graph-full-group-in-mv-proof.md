---
rg: 2
id: brick-coded-two-graph-full-group-in-mv-proof
kind: route
title: Nested bricks give a conjugacy of path space with Cantor cubes, and cylinder maps become prefix replacements
target: brick-coded-two-graph-full-groups-embed-in-brin-thompson
requires: []
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
---

Full proof: Part 0 (factorization) and Part A, Steps A1–A6, of the artifact. Outline:

1. **Extension to rectangles.** By (B2) and flip connectivity of monotone lattice paths,
   `φ` extends to rectangles with `φ(λρ) = φ(λ)φ(ρ)`.
2. **Factorization.** Rectangles of degree `(p+1,q)` at `a` correspond bijectively to
   pairs `(e, ρ)` with `ρ` of degree `(p,q)` at `t(e)`: fill the first column cell by
   cell from the bottom with the square bijection.
3. **A1.** The bricks `[φ(x_n)]` are nested. By (B3), `|φ_j(x_{kN})| ≥ k`. So `h(x)` is
   one point and `h` is continuous.
4. **A2.** For every `(p,q)` and every vertex `a`, the bricks `[φ(λ)]` with
   `λ ∈ Λ^{(p,q)}(a)` partition `C^m`. The induction uses factorization, (B1), and the
   fact that `z ↦ φ(e)z` is a bijection `C^m -> [φ(e)]`.
5. **A3.** `h` is injective by A2 applied to distinguishing corners. It is surjective by
   the unique nested choice of corners. Being continuous from a compact space, it is a
   homeomorphism with `h(Z(λ)) = [φ(λ)]`.
6. **A4.** `h(λz) = φ(λ)h(z)`, because the regions `[0,p+n]×[0,q+n]` are cofinal and
   factor as `λ z_n`.
7. **A5.** `h g h^{-1}` maps `[φ(μ_k)]` canonically onto `[φ(λ_k)]`, and both families
   partition `⊔_a C^m`.
8. **A6.** Chart by a complete prefix code `{u_a}` in the first coordinate. The partitions
   need not be guillotine, so refine the domain to a uniform grid `G_L`, and subdivide
   each image brick uniformly to `G_R`. The pulled-back pieces are uniform subdivisions
   of grid bricks. Both partitions are then dyadic, and the map is canonical on each
   piece, so it lies in Brin's `mV`. Conjugation is injective and multiplicative.
