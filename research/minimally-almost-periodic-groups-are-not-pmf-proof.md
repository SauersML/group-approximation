---
rg: 2
id: minimally-almost-periodic-groups-are-not-pmf-proof
kind: route
title: Trivial finite-dimensional representations cannot reproduce the reduced norm of 1 - g; Malcev plus simplicity removes all finite quotients
target: minimally-almost-periodic-groups-are-not-pmf
requires:
  - steinberg-elementary-groups-are-simple-mod-centre
  - simple-kazhdan-lef-group-from-minimal-subshift
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

Artifact §2.1, Proposition 4.

1. **No PMF.** Pick `g ≠ e` and `z = 1 − g ∈ ℂ[Γ]`. Every finite-dimensional unitary representation `ρ_i` is
   trivial, so `ρ_i(z) = 0`. Since `λ_g ≠ 1`, `‖λ_Γ(z)‖ > 0`. So `‖ρ_i(z)‖` does not tend to `‖λ_Γ(z)‖`.
2. **Malcev criterion.** For a homomorphism `ρ: Γ → U(d)`, the image is a finitely generated subgroup of
   `GL_d(ℂ)`, hence residually finite (Malcev's theorem, standard). If `ρ(Γ) ≠ 1` it has a nontrivial finite
   quotient, which is also a quotient of `Γ`.
3. **Application.** `steinberg-elementary-groups-are-simple-mod-centre` gives, for `G = EL_N(A_k(𝒢))`, `N ≥ 3`:
   - every normal subgroup of `G` is central or all of `G`;
   - `Z(G) ⊆ k^× I_N`, which is finite for finite `k`;
   - `G` is infinite and finitely generated.

   If `G/M` is a finite quotient with `M ≠ G`, then `M ⊆ Z(G)` is finite, so `G/M` is infinite, which is absurd. So
   `G` has no nontrivial finite quotient, and the same holds for `G/Z(G)`. Item 2 then applies.
   - **Pestov's group.** `simple-kazhdan-lef-group-from-minimal-subshift` provides `S` infinite, finitely generated
     and simple, so item 2 applies to it directly.
   - **Boundary-action group.** It is covered by the Steinberg theorem, with `LC(∂F_d,k)⋊F_d` the Steinberg algebra
     of the transformation groupoid.
