---
rg: 2
id: minimal-effective-steinberg-algebras-have-scalar-centre-proof
kind: route
title: Central elements live on the interior of the isotropy and are invariant, hence constant
target: minimal-effective-steinberg-algebras-have-scalar-centre
requires: []
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
---

Complete proof in artifact §2.
1. `z` central and `U ⊆ 𝒢⁽⁰⁾` clopen: `χ_(𝒢⁽⁰⁾∖U) z χ_U = χ_(𝒢⁽⁰⁾∖U) χ_U z = 0`. So `z(g) = 0` whenever `s(g) ∈ U` and
   `r(g) ∉ U`. Clopens separate points, so `supp z ⊆ Iso(𝒢)`.
2. `supp z` is open (`z` is locally constant with compact support), so `supp z ⊆ Iso(𝒢)° = 𝒢⁽⁰⁾` by effectiveness.
3. For a compact open bisection `B`, `χ_B z = z χ_B` gives `z(r g) = z(s g)` for `g ∈ B`. So `z` is constant on
   orbits.
4. `z` is continuous and every orbit is dense, so `z` is constant.
