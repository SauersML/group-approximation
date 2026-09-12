---
rg: 2
id: perfect-unit-subgroups-elementary-proof
kind: route
title: Whitehead's lemma puts every commutator of units into E_2
target: perfect-unit-subgroups-embed-in-elementary-groups
requires: []
---

Derivation, elementary, over an arbitrary unital ring `R`.

1. **Whitehead's lemma.** For `u in R^x` put
   `w(u) = e_12(u) e_21(-u^-1) e_12(u)`. Multiplying out,
   `e_12(a) e_21(b) = [[1+ab, a], [b, 1]]`, and then with `a = u`, `b = -u^-1`,
   `c = u` the product `e_12(a) e_21(b) e_12(c)` is `[[0, u], [-u^-1, 0]]`.
   So `w(-1) = [[0,-1],[1,0]]` and

       w(u) w(-1) = [[u, 0], [0, u^-1]] = diag(u, u^-1).

   The row-by-row computation uses no commutativity. Hence `diag(u, u^-1)` lies
   in `E_2(R)` for every unit `u`.
2. **Commutators.** For units `u, v`,

       diag(u, u^-1) diag(v, v^-1) diag((vu)^-1, vu) = diag(u v u^-1 v^-1, 1),

   so `diag([u,v], 1) in E_2(R)`.
3. **Perfect subgroups.** `u |-> diag(u, 1)` is an injective homomorphism
   `R^x -> GL_2(R)`. Every element of `P = [P,P]` is a finite product of
   commutators `[u,v]` with `u, v in P`, so its image is a product of elements
   of `E_2(R)`. Hence `P -> E_2(R)` injectively.
4. **Higher rank.** The block inclusion `GL_2(R) -> GL_n(R)`,
   `x |-> diag(x, I_(n-2))`, sends `e_ij(r)` to `e_ij(r)`, so it maps `E_2(R)`
   into `E_n(R)`. Composing gives `P -> E_n(R)` for every `n >= 2`. `∎`
