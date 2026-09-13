---
rg: 2
id: steinberg-algebras-have-local-annihilation-proof
kind: route
title: Small clopen sets near each unit are separated from their own translates by a far clopen set
target: steinberg-algebras-have-local-annihilation
requires: []
artifacts:
  - research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md
---

Complete proof in `research/artifacts/un-steinberg-elementary-simplicity-2026-09-13.md` §1.

1. Restriction identity: for compact open `U, W ⊆ 𝒢⁽⁰⁾`, `χ_W f χ_U` is `f` restricted to the arrows from `U` to `W`.
2. Take `K = B_1 ∪ … ∪ B_m ⊇ supp F`, with partial homeomorphisms `α_j : s(B_j) → r(B_j)`. For a unit `x`, the set
   `P_x = {x} ∪ {α_j(x)}` is finite. Pick `y ∉ P_x` (the unit space is infinite) and a clopen `W ∋ y` missing `P_x`.
   Continuity of the `α_j` and clopenness of the `s(B_j)` give a clopen `V_x ∋ x` with `V_x ∩ W = ∅` and
   `α_j(V_x ∩ s(B_j)) ∩ W = ∅`.
3. For clopen `V ⊆ V_x` and any `a`, set `t = χ_W ≠ 0` and `s = χ_V a`. Then `ts = 0`, and `tfs = (χ_W f χ_V) a = 0`,
   because every arrow of `K` with source in `V` has range in `⋃_j α_j(V_x)`, which misses `W`.
4. By compactness, refine to a clopen partition `V_1, …, V_r` subordinate to the `V_(x_i)`. Then `a = Σ χ_(V_i) a`.
