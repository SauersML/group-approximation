---
rg: 2
id: central-halving-closed-bauer-face-triviality-proof
kind: route
title: Push the central halving sequence into the face bundle and apply Ozawa's Theorem 15 (ii)
target: central-halving-trivializes-every-closed-bauer-face-bundle
requires:
  - closed-extreme-trace-sets-give-r-fibre-w-star-bundles
  - r-fibre-bundle-triviality-iff-uniform-central-halving
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Section 2 of the artifact (Theorem A).

1. By the first prerequisite, `M_K` is a strictly separable continuous W*-bundle over
   `K`, with all fibres `R`, and `‖·‖_{2,u} = ‖·‖_{2,F} ≤ ‖·‖_{2,T(A)}`.
2. The images of `p_n` in `M_K` satisfy `0 ≤ p_n ≤ 1`, `‖p_n − p_n²‖_{2,u} → 0` and
   `‖E(p_n) − 1/2‖ → 0`. Also `‖[p_n, a]‖_{2,u} → 0` for `a ∈ A`.
3. The unit ball of `A` is `‖·‖_{2,u}`-dense in that of `M_K`. For contractions,
   `‖[p_n, x]‖_{2,u} ≤ ‖[p_n, a]‖_{2,u} + 2‖x − a‖_{2,u}`, so the sequence is central
   in `M_K`.
4. This is condition (ii) of the second prerequisite, so `M_K ≅ C_σ(K,R)`.
5. The dictionary clause of the first prerequisite gives relative divisibility for
   every `N`.

Ozawa's proof of (ii) ⟹ (iii) derives `‖E(p_n a) − E(p_n)E(a)‖ → 0` from factoriality
of the fibres (MSI copy, lines 1060–1075). So no balancing hypothesis is needed.
