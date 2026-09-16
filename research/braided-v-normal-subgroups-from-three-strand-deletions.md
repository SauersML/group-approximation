---
rg: 2
id: braided-v-normal-subgroups-from-three-strand-deletions
kind: claim
title: Every normal subgroup of B_3 inside [PB_3, PB_3] is the three-strand stage of a normal subgroup of bV
artifacts:
  - research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md
---

Let `M` be a normal subgroup of `B_3` with `M ≤ [PB_3, PB_3]`. For each `n`, let

    G_n(M) = { p ∈ [PB_n, PB_n] : pi_S(p) ∈ M for every 3-element S ⊆ {1..n} },

where `pi_S : PB_n -> PB_3` deletes every strand not numbered by `S`.

Then:

- `(G_n(M))_n` is a complete coherent sequence of normal subgroups of the `B_n`, in the sense of
  arXiv:1403.8132v2 §4: `clone_k(PB_n) ∩ G_{n+1}(M) = clone_k(G_n(M))` for all `1 ≤ k ≤ n`.
- `N_M = {(T, p, T) : p ∈ G_{n(T)}(M)}` is a normal subgroup of `bV = V_br` contained in `[P_br, P_br]`.
- For every tree `T` with three leaves, `N_M ∩ PB_T = {(T, p, T) : p ∈ M}`.

In particular `M ≤ M'` if and only if `N_M ≤ N_{M'}`, so `M -> N_M` is injective and order-preserving.

Special cases:

- `M = [PB_3, PB_3]` gives `N_M = [P_br, P_br]`.
- `M = 1` gives Zaremsky's 3-loose subgroup `Th(Lambda_*(3))`.
