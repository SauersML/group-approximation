---
rg: 2
id: virtually-raag-groups-in-2v-via-finite-extensions
kind: route
title: Virtual overgroups of right-angled Artin groups reach 2V through the Kaloujnine-Krasner embedding and wreath products in nV
target: virtually-special-groups-embed-in-brin-thompson-group-2v
requires:
  - every-raag-embeds-in-brin-thompson-group-2v
---

Full proof: Part D of the artifact. Here `C = {0,1}^N`.

1. **D1 (wreath closure).** If `H ≤ nV` and `k ≥ 2`, then `H ≀ S_k` embeds in
   `nV`.
   - Take the bricks `Q_i = 1^{i-1}0C × C^{n-1}` (`i < k`) and
     `Q_k = 1^{k-1}C × C^{n-1}`, a dyadic subdivision of `C^n`. Let
     `κ_i : C^n → Q_i` be the canonical prefix insertion.
   - For `h ∈ nV`, let `h^{(i)}` be `κ_i h κ_i^{-1}` on `Q_i` and the identity
     elsewhere. Transporting the subdivisions of `h` into `Q_i` shows
     `h^{(i)} ∈ nV`.
   - For `τ ∈ S_k`, let `P_τ = κ_{τ(i)} κ_i^{-1}` on each `Q_i`. Then
     `P_τ ∈ nV`, `P_τ P_ρ = P_{τρ}`, `P_τ h^{(i)} P_τ^{-1} = h^{(τ(i))}`, and
     copies in different pieces commute.
   - So `(h_1, …, h_k; τ) ↦ h_1^{(1)} ⋯ h_k^{(k)} P_τ` is a homomorphism. It is
     injective: the `h^{(i)}` preserve each `Q_j`, so trivial image forces
     `τ = id`, and then every `h_i = id`.
2. **D2 (Kaloujnine–Krasner).** If `N ⊴ G` has index `k`, then `G ≤ N ≀ S_k`.
   Choose coset representatives `t_i`, write `g t_i = t_{τ_g(i)} n_i(g)`, and let
   `g` act on `⊔_i N` by block permutation `τ_g` and left multiplication by
   `n_i(g)` inside blocks. This is the left regular action of `G` in coordinates,
   so it is faithful.
3. **D3.** Let `H ≤ G` have finite index with `H ≤ A_Γ`. Its normal core
   `N = ⋂_g gHg^{-1}` has finite index `k` and `N ≤ H ≤ A_Γ ≤ 2V` by
   `every-raag-embeds-in-brin-thompson-group-2v`. By D2 and D1 with `n = 2`,
   `G ≤ N ≀ S_k ≤ 2V`. ∎

Belk–Bleak–Matucci (arXiv:1602.08635, p. 2) record the same finite-extension
closure through the Bleak–Salazar-Díaz wreath product theorem; D1–D3 are a
direct proof.
