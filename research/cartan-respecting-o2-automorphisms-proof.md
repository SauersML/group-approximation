---
rg: 2
id: cartan-respecting-o2-automorphisms-proof
kind: route
title: Check the invariant Cartan subalgebra and apply Barlak--Li Proposition 1.6
target: cartan-respecting-o2-automorphisms-give-uct-crossed-products
requires: [barlak-li-cartan-subalgebras-force-uct]
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**General statement.**  `O_2` is separable and nuclear, and a crossed product by a
finite group preserves nuclearity.  If `α(B) = B` for a Cartan subalgebra
`B ⊆ O_2`, Barlak--Li Proposition 1.6 (with `Γ = Z_n`) gives the UCT for
`O_2 ⋊_α Z_n`.

**Family 1.**  Let `u` normalize `D_2`, i.e. `u D_2 u* = D_2`.  The generators
`s_i` are partial isometries normalizing `D_2`, since `s_i s_μ s_μ* s_i* =
s_{iμ} s_{iμ}*` and `s_i* s_{μ} s_{μ}* s_i` is `s_{μ'} s_{μ'}*`, `1` or `0`.
Products of normalizing partial isometries normalize, so each `λ_u(s_i) = u s_i`
normalizes `D_2`, and so does `λ_u(s_μ) = λ_u(s_{μ_1}) ⋯ λ_u(s_{μ_k})`.  For a
partial isometry `v` normalizing `D_2` we have `v v* = v · 1 · v* ∈ D_2`, because
`1 ∈ D_2`.  Hence `λ_u(s_μ s_μ*) = λ_u(s_μ) λ_u(s_μ)* ∈ D_2`, and `λ_u(D_2) ⊆ D_2`,
since `D_2` is the closed span of the `s_μ s_μ*`.  When `λ_u` is an automorphism,
`λ_u(D_2)` is a masa contained in the masa `D_2`, so `λ_u(D_2) = D_2`.  Thompson's
`V` consists of unitaries `Σ_j s_{μ_j} s_{ν_j}*` over pairs of complete prefix
codes.  They map `s_ν s_ν*` to `s_{μ'} s_{μ'}*` and so normalize `D_2`, as do all
unitaries of `D_2`.

**Family 2.**  `D_2 ⊗ D_2` is a Cartan subalgebra of `O_2 ⊗ O_2`: it is the
algebra of the unit space of the product of the Renault groupoids of
`(O_2, D_2)` with itself, which is again étale, Hausdorff, locally compact,
second countable and topologically principal.  Renault's theorem (as recalled in
Barlak--Li, Section 2) makes the unit-space algebra of such a groupoid a Cartan
subalgebra.  The flip preserves `D_2 ⊗ D_2`, so `θ ∘ σ ∘ θ^{-1}` preserves the
Cartan subalgebra `θ(D_2 ⊗ D_2)` of `O_2`.
