---
rg: 2
id: pure-loop-braid-group-is-colimit-of-cabling-stabilizers
kind: claim
title: "For n ≥ 7, PLB_n is the amalgam of its vertex stabilizers along edge stabilizers over the fundamental domain OM(K_n) of L_n(LB_*)"
artifacts:
  - research/artifacts/zp-loop-braid-descending-links-simply-connected-2026-09-16.md
---

Let `P = PLB_n = PΣAut_n` act by left multiplication on the descending link `L_n(LB_*)`. This is the
complex of Witzel–Zaremsky, arXiv:1405.5491v3, §5.3, for the loop braid cloning system of their §10.

- The simplices `[s, Γ]` with s a permutation braid form a strict fundamental domain Q. Stabilizers fix
  simplices pointwise, and `Q ≅ OM(K_n)` via `[s, e_k] ↦ (ρ(s)k, ρ(s)(k+1))`.
- The stabilizer of `[s, Γ]` is `s · (PLB_{n−|Γ|})κ_Γ · s^{-1}`.

Claim: for `n ≥ 7`, the natural map to P is an isomorphism, from

`(∗_{v ∈ V(Q)} P_v) / ⟨⟨ ι_v(g) = ι_w(g) : {v, w} an edge of Q, g ∈ P_{{v,w}} ⟩⟩`.

The fundamental-domain and stabilizer statements are proved in artifact §2 (Lemmas 2.2–2.4). The
isomorphism is artifact Theorem 6.1.
