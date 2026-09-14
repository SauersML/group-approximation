---
rg: 2
id: subshift-el3-acts-two-transitively-on-orbit-modules
kind: claim
title: EL_3(LC(X,F_2)⋊Z) acts on every orbit module transitively on linearly independent tuples, hence faithfully and 2-transitively on a countable set
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `subshift-el3-acts-two-transitively-on-orbit-modules-proof`.

Let `X` be an infinite minimal subshift, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`. For `x ∈ X`, the orbit module is `V_x = F_2[Z]`, with `f δ_n = f(T^n x) δ_n` and `u δ_n = δ_{n+1}`.

For every `k ≥ 1`, `G` acts on `V_x^3` transitively on ordered `k`-tuples of linearly independent vectors. So `G` acts faithfully and 2-transitively on the countable set `V_x^3 ∖ {0}`.

The mechanism: finitely many vectors lie in one pass of a tower with disjoint levels `T^aV`, and the tower copy of `GL_{3h}(F_2)` lies in `G`.

**Review (sk-verify-15, 2026-09-13): PASS.** Tower action on orbit-module blocks (ε_ab δ_m formula, gaps ≥ h), transitivity on independent tuples, faithfulness and 2-transitivity re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part2.md` §1.
