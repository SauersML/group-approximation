---
rg: 2
id: car-bernoulli-crossed-product-is-lamplighter-ring-proof
kind: route
title: Direct proof that the binary lamplighter crossed product is the Bernoulli CAR crossed product
target: car-bernoulli-crossed-product-is-lamplighter-ring
requires: []
artifacts:
  - research/artifacts/sk-strong-5-second-family-2026-09-13.md
---

Write `N = ⊕_Z Z/2 ⊴ L`, so `L = N ⋊ ⟨s⟩` and `LC(2^Z) ⋊ L = (LC(2^Z) ⋊ N) ⋊ ⟨s⟩`. The unique normal form
`Σ_ℓ f_ℓ u_ℓ` over `ℓ = n s^j` gives the unique form `Σ_j b_j s^j` with `b_j = Σ_n f_{n,j} u_n`.

1. **Finite windows.** Put `H_n = (Z/2)^{[−n,n]}`. Let `A_n` be the span of `f u_h` with `f` depending only on the
   coordinates in `[−n,n]` and `h ∈ H_n`; it is `LC(H_n, F_2) ⋊ H_n` for `H_n` acting on itself by translation. The map
   `f u_h ↦ M_f λ_h` on `F_2^{H_n}`, with `λ_h δ_y = δ_{y+h}`, is an algebra homomorphism. It is onto, since
   `M_{δ_x} λ_{x−y} δ_z = [z = y] δ_x` gives every matrix unit `E_{x,y}`. Both sides have dimension `|H_n|^2`, so
   `A_n ≅ M_{2^{2n+1}}(F_2)`. Since `F_2^{H_n} = ⊗_{t∈[−n,n]} F_2^2` and both `f` and `h` factor over sites,
   `A_n ≅ ⊗_{t∈[−n,n]} M_2(F_2)`, with site `t` spanned by `δ_{x_t=i}` and the flip at `t`.
2. **Inclusions.** A function of the coordinates in `[−n,n]`, viewed on `[−n−1,n+1]`, is `M_f ⊗ 1`, and `h ∈ H_n` acts
   as `λ_h ⊗ 1`. So `A_n ⊆ A_{n+1}` is `x ↦ 1 ⊗ x ⊗ 1`, and `LC(2^Z) ⋊ N = ⋃_n A_n ≅ B`. Every element involves finitely
   many cylinder functions and finitely many flips, so the union is everything.
3. **The shift.** `s f s^{-1} = f ∘ T^{-1}` and `s u_h s^{-1} = u_{σ(h)}` move site `t` to site `t+1` in both factors.
   So conjugation by `s` is the tensor shift `σ` on `B`, and `LC(2^Z) ⋊ L ≅ B ⋊_σ Z`. ∎
