---
rg: 2
id: subshift-el3-has-continuum-many-maximal-subgroup-classes-proof
kind: route
title: Point stabilizers of the 2-transitive orbit-module actions are maximal and pairwise distinct, and G is countable
target: subshift-el3-has-continuum-many-maximal-subgroup-classes
requires: [subshift-el3-acts-two-transitively-on-orbit-modules]
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md
---

Full proof: artifact §2.
- **Maximal.** By `subshift-el3-acts-two-transitively-on-orbit-modules`, `G` acts 2-transitively on `Ω_x = V_x^3 ∖ {0}`. A 2-transitive action is primitive, so point stabilizers are maximal. The index is `|Ω_x| = ℵ_0`.
- **Distinct.** For `f ∈ LC(X,F_2)`, `e_21(f)(δ_0 e_1) = δ_0 e_1 + f(x) δ_0 e_2`, so `e_21(f) ∈ H_x` iff `f(x) = 0`. For `x ≠ y`, a clopen `U ∋ y` with `x ∉ U` gives `e_21(e_U) ∈ H_x ∖ H_y`.
- **Counting.** `X` is perfect compact metrizable, so `|X| = 2^{ℵ_0}`. `G` is countable, so every conjugacy class of subgroups is countable. So there are continuum many classes. Transitive `G`-sets are isomorphic iff their stabilizers are conjugate. ∎
