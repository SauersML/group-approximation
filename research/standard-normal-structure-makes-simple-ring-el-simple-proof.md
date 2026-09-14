---
rg: 2
id: standard-normal-structure-makes-simple-ring-el-simple-proof
kind: route
title: Specialize the Preusser and Vaserstein sandwich theorems to simple rings
target: standard-normal-structure-makes-simple-ring-el-simple
requires: [preusser-exchange-rings-have-standard-normal-subgroups, vaserstein-local-stable-range-normal-subgroups]
artifacts:
  - research/artifacts/sk-stable-rank-a-shortcut-2026-09-13-part1.md
---

Let `H ≤ GL_n(R)` be normalized by `EL_n(R) = E_n(R)`, with `n ≥ 3`.

**The centre of `GL_n(R)`.** A matrix commuting with every `e_ij(1)` is scalar, `cI`. Commuting with every `e_ij(r)`
forces `c ∈ Z(R) = k`. So `Center(GL_n(R)) = k^× I_n`, and `Z(EL_n(R)) = EL_n(R) ∩ k^× I_n`.

**Exchange case.** By Preusser's Theorem 3, `E_n(R,I) ⊆ H ⊆ C_n(R,I)` for an ideal `I`. Since `R` is simple, `I = 0` or `I = R`.
- `I = R`: then `E_n(R,R) = E_n(R) ⊆ H`.
- `I = 0`: then `C_n(R,0) = Center(GL_n(R)) = k^× I_n`, so `H` is central.

**Stable-range case.** The centre `C = k` has the single maximal ideal `D = 0`. Take `S = {1}`, so `S^{-1}R = R` and
`sr(S^{-1}R) ≤ n − 1`. Vaserstein's Theorem 4 then gives statement (2): for a unique ideal `B`, the image of `H` in
`GL_n(R/B)` is central and `H ⊇ [E_n R, E_n B]`.
- `B = R`: `H ⊇ [E_n R, E_n R] = E_n R`, because `e_ij(r) = [e_ik(r), e_kj(1)]` for distinct `i, j, k`.
- `B = 0`: `H` is central in `GL_n(R)`.

**Conclusion.** If `N ⊴ EL_n(R)`, then `N` is normalized by `EL_n(R)`, so `N ⊆ Z(EL_n(R))` or `N = EL_n(R)`.
Normal subgroups of the quotient by the centre correspond to normal subgroups containing the centre, so the quotient
is simple. It is nontrivial because `e_12(1)` and `e_21(1)` do not commute.
