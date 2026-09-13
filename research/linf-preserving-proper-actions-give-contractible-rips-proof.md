---
rg: 2
id: linf-preserving-proper-actions-give-contractible-rips-proof
kind: route
title: The orbit is a periodic discrete set with an invariant l-infinity proximity complex acted on vertex-transitively
target: linf-preserving-proper-actions-give-contractible-rips
requires:
  - periodic-linf-proximity-complexes-are-contractible
  - flag-complex-proper-vertex-transitive-action-rips
---

Let `O = G x_0`.

1. **`O` is discrete, and stabilizers are finite.** Apply hypothesis 1 to a closed
   ball `C` around any point: only finitely many `g` send `x_0` into `C`, so `O ∩ C`
   is finite, and the stabilizer of `x_0` is finite.
2. **`O` is `Λ`-periodic.** By hypothesis 3, `O + e_i ⊆ O` for every `i`, and `−e_i`
   is also realized by the inverse element. So `O + Λ = O` for `Λ = ⊕ Z e_i`.
3. **Contractible complex.** By `periodic-linf-proximity-complexes-are-contractible`,
   the flag complex `K_c(O)` of the graph "`u ≠ w` adjacent iff `‖u − w‖_∞ <= c`" is
   contractible for `c >= 4`. It is locally finite by step 1.
4. **Invariance.** For `g ∈ G` and `u, w ∈ O`, `g u − g w = A_g (u − w)`. By
   hypothesis 2, `A_g` permutes coordinates up to sign, so
   `‖A_g(u − w)‖_∞ = ‖u − w‖_∞`. So `G` acts on the graph, and hence simplicially on
   `K_c(O)`, transitively on its vertex set `O`, with finite vertex stabilizers
   (step 1).
5. **Conclusion.** Apply `flag-complex-proper-vertex-transitive-action-rips` with
   `v = x_0`. The generating set it produces is exactly
   `{g ≠ 1 : g x_0 = x_0 or ‖g x_0 − x_0‖_∞ <= c} = S_c`, and `P_1(G, S_c)` is
   contractible.
