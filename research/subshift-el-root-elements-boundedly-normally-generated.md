---
rg: 2
id: subshift-el-root-elements-boundedly-normally-generated
kind: claim
title: In EL_3(LC(X,F_2)⋊Z) every nontrivial g normally generates all root elements in boundedly many steps, so all normal generation norms are bi-Lipschitz to the root length
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
---

**Statement.** Let `X` be an infinite minimal subshift and `G = EL_3(LC(X,F_2) ⋊ Z)`.
1. For every `g ∈ G∖{e}` there is `M_g < ∞` such that every root element `e_ij(r)`, `r ∈ R`, is a product of at most `M_g` conjugates of `g^{±1}`. More precisely `M_g ≤ 2(2⌊1/inf_μ μ(V_g)⌋ + 2)M′_g`, where `M′_g` conjugates of `g^{±1}` give `e_12(χ_{V_g})` for a nonempty clopen `V_g`.
2. Let `λ^c(h)` be the least number of conjugates of root elements with product `h`. Then `λ^c(h) ≤ λ^c(g)ν_g(h)` and `ν_g(h) ≤ M_g λ^c(h)`, so every normal generation norm `ν_g` is bi-Lipschitz to `λ^c`.
3. So `G` is bounded in the sense of Burago–Ivanov–Polterovich (every conjugation-invariant norm is bounded) iff `λ^c` is bounded. That holds: `λ^c ≤ 78` by `subshift-el-groups-boundedly-elementary-generated`, which gives `subshift-el-groups-have-bounded-conjugation-invariant-norms`.

**Status: established** by `subshift-el-root-elements-boundedly-normally-generated-proof`. UNREVIEWED; queued with sk-verify-13.

**Review (sk-verify-15, 2026-09-13): PASS.** Commutator in the tower copy of GL_d(F_2), finite simplicity, Theorem B with U = X and ρ_min ≥ 1, and the permutation-conjugate step re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part2.md` §3.
