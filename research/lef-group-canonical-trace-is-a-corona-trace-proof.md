---
rg: 2
id: lef-group-canonical-trace-is-a-corona-trace-proof
kind: route
title: "Regular representations of finite local models realize the canonical trace in the corona; trace one at the identity only"
target: lef-group-canonical-trace-is-a-corona-trace
requires: []
---

- **(a)** Let τ_G = tr_ω∘Φ. Then g ↦ Φ(u_g) is a homomorphism G → U(Q_d). If Φ(u_g) = 1, then
  τ_G(u_g) = tr_ω(1) = 1, so g = e. Hence G embeds in U(Q_d), i.e. G is operator MF.
- **(b)** Exhaust G by finite windows B_1 ⊆ B_2 ⊆ … . LEF gives maps σ_k: B_k → F_k into finite groups,
  injective, with σ_k(gh) = σ_k(g)σ_k(h) whenever g, h, gh ∈ B_k.
  - Put Θ_k(g) = λ_{F_k}(σ_k(g)) for g ∈ B_k and 1 otherwise, with d_k = |F_k|.
  - Each pair g, h and gh lies in B_k for all large k, so Θ = [Θ_k]: G → U(Q_d) is a homomorphism, and it
    extends to a unital *-homomorphism Φ on C*_max(G) by the universal property.
  - tr λ_{F_k}(x) = [x = e]. σ_k(e) = e because σ_k(e)² = σ_k(e), and σ_k(g) ≠ e for g ≠ e once e, g ∈ B_k.
  - So tr_ω Φ(u_g) = δ_{g,e} = τ_G(u_g). Both are states agreeing on the spanning unitaries, so
    tr_ω∘Φ = τ_G. ∎

Full text: `research/artifacts/un-traces-2026-09-13-part1.md` §4.
