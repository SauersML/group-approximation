---
rg: 2
id: braided-v-has-continuum-many-normal-subgroups-proof
kind: route
title: Transfer the continuum of normal subgroups of B_3 inside PB_3'' to bV along three-strand deletions
target: braided-v-has-continuum-many-normal-subgroups
requires:
  - braided-v-normal-subgroups-from-three-strand-deletions
  - b3-has-continuum-many-normal-subgroups-in-pb3-commutator
artifacts:
  - research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md
---

Artifact §5 (Theorem D (a), (b)).

1. By `b3-has-continuum-many-normal-subgroups-in-pb3-commutator`, there are `2^aleph_0` normal subgroups `M` of
   `B_3` with `M ≤ PB_3'' ≤ [PB_3, PB_3]`. There is also a strictly ascending chain `M_1 < M_2 < …` of them.
2. By `braided-v-normal-subgroups-from-three-strand-deletions`, each such `M` gives a normal subgroup `N_M` of
   `V_br` with `N_M ≤ [P_br, P_br]`, and `M ≤ M'` if and only if `N_M ≤ N_{M'}`.
   - So `M -> N_M` is injective, which gives `2^aleph_0` distinct normal subgroups of `V_br`.
   - And `N_{M_1} < N_{M_2} < …` is strictly ascending.
3. `V_br` is countable (triples of finite data), so it has at most `2^aleph_0` subgroups. Hence it has exactly
   `2^aleph_0` normal subgroups.
4. Let `N_infinity = ∪_k N_{M_k}`. It is normal as the union of a chain of normal subgroups. Suppose
   `N_infinity = <<x_1, …, x_r>>`. All `x_i` lie in some `N_{M_K}`, so `N_infinity ≤ N_{M_K} < N_{M_{K+1}}`, a
   contradiction.
5. **`F_br`.** `P_br = {(T, p, T) : p pure}` lies in `F_br = {(T_-, p, T_+) : p pure}`. Each `N_M ≤ P_br` is
   normal in `V_br`, hence normal in the subgroup `F_br`. `F_br` is countable. So steps 2–4 apply verbatim to
   `F_br`: it has exactly `2^aleph_0` normal subgroups, continuum many inside `[P_br, P_br]`, and the same
   strictly ascending chain.
