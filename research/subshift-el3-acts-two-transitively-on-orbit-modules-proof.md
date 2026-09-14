---
rg: 2
id: subshift-el3-acts-two-transitively-on-orbit-modules-proof
kind: route
title: Finitely many vectors of an orbit module lie in one tower pass, where a copy of GL_{3h}(F_2) inside G moves them freely
target: subshift-el3-acts-two-transitively-on-orbit-modules
requires: [simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md
---

Full proof: artifact §0–§1.

**Tower copy.** Let `V ≠ ∅` be clopen with `V ∩ T^jV = ∅` for `0 < |j| < h`. Put `ε_ab = e_{T^aV}u^{a−b}` for `0 ≤ a,b < h`.
- These are matrix units, `ε_ab ε_{a′b′} = δ_{ba′} ε_{ab′}`, so `ψ(M) = Σ M_ab ε_ab` embeds `M_h(F_2)` into `R`.
- `ι(M) = I − eI + ψ(M)` embeds `GL_{3h}(F_2) = EL_3(M_h(F_2))` into `G`, since `ι(e_pq(E_ab)) = e_pq(ε_ab)`.

**Action on `V_x`.** `ε_ab δ_m = [T^{m−b}x ∈ V] δ_{m−b+a}`.
- The visit times `n` of `x` to `V` have gaps `≥ h`, so the blocks `span{δ_{n+c} : c < h}` are disjoint.
- `ι(M)` acts as `M` on each block `^3` and as the identity off the blocks.

**Transitivity.** Suppose two independent `k`-tuples are supported in `[p, p+L)`.
- Take `V ∋ T^p x` with disjoint translates up to `L` (aperiodicity), and `h = L`.
- `GL_{3L}(F_2)` carries one tuple to the other on the block at `p`.

**Faithfulness.** The action is nontrivial (`e_12(1) δ_0e_2 = δ_0e_1 + δ_0e_2`), and `G` is simple with trivial centre (`simple-kazhdan-lef-group-from-minimal-subshift`, `F_2^× = 1`).

Over `F_2`, two distinct nonzero vectors are independent, so the action is 2-transitive. ∎
