---
rg: 2
id: morphic-sft-matricial-iff-scale-one-torus-module-proof
kind: route
title: Induce a covariant family from the scale-1 module, double its scale along the morphism tower, restrict to period tori, descend, and apply the torus criterion
target: morphic-sft-matricial-iff-scale-one-torus-module
requires:
  - torus-quantum-tilings-decide-matriciality-of-sft-rings
  - torus-tiling-modules-restrict-to-smaller-scales
  - morphism-towers-double-covariant-tiling-scales
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
---

Artifact §6, Theorem B. Here TC is `torus-quantum-tilings-decide-matriciality-of-sft-rings` with parts (a)–(d) of
its artifact §2, and DESC is `torus-tiling-modules-restrict-to-smaller-scales`.

- **(⇒)** By TC(d) there is a nonzero finite-dimensional `𝒯_(D,Λ)(Ω,k)`-module at `D = max(r,1)`. By DESC it is a
  `𝒯_(1,Λ)(Ω,k)`-module.
- **(⇐)**
  - TC(a) turns the scale-`1` module into a nonzero finite-dimensional covariant `1`-family over `k`.
  - Iterating `morphism-towers-double-covariant-tiling-scales` with `Ω_S = Ω_T = Ω` gives nonzero finite-dimensional
    covariant `2^n`-families over `k` for every `n`. (H1) and (H2) are the hypotheses on `ω`.
  - TC(b) (`k` finite) gives, for every `n`, a nonzero module of some `𝒯_(2^n,Λ_n)(Ω,k)`.
  - DESC gives one at every scale `D`.
  - TC(d) (⇐) gives the unital embedding. ∎
