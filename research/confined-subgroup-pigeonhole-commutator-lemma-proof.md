---
rg: 2
id: confined-subgroup-pigeonhole-commutator-lemma-proof
kind: route
title: Confinement at each chosen conjugator, then pigeonhole on the r+1 witnesses
target: confined-subgroup-pigeonhole-commutator-lemma
requires: []
---

**Proof.**
- For each `i`, confinement at `g = g_i` gives `p_i ∈ P ∩ g_iHg_i^{-1}`, so `h_i = g_i^{-1}p_ig_i ∈ H`.
- Among `r+1` indices two share a value, `p_i = p_j = p` with `i ≠ j`.
- Put `k = g_ig_j^{-1}`, so `g_j = k^{-1}g_i`. Then `h_j^{-1} = g_j^{-1}p^{-1}g_j = g_i^{-1}kp^{-1}k^{-1}g_i`, and
  `h_ih_j^{-1} = g_i^{-1}(p·kp^{-1}k^{-1})g_i = g_i^{-1}[p,k]g_i ∈ H`. ∎

(R′) and (R″) follow by applying this to `n = r+1` conjugators with the stated property. Details: `research/artifacts/sk-cstar-genericity-2026-09-14-part1.md` §1.
