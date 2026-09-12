---
rg: 2
id: fpbs-twisted-level-graph-generates-cyclic-extension-proof
kind: route
title: Decompose transport paths inside an N-orbit into return moves, and read the Bernoulli labels at distinct group elements
target: fpbs-twisted-level-graph-generates-cyclic-extension
requires: []
---

Written derivation. Throughout, `t^-m s t^m = phi^-m(s)` for `s in N`.

1. **Cost.** `t` costs `1`, and each `s|_A` costs `mu(A)`.
2. **Return moves are transport paths.** Let `t^m z in A`. Then `z -> t^m z -> s t^m z -> t^-m s t^m z = phi^-m(s) z` is a `Phi_A`-path, so every edge of `G_A` lies in `R_(Phi_A)`.
3. **(1), the "if" direction.** If `G_A` is connected on almost every `N`-orbit, then `R_(Phi_A)` contains `R_N`. It also contains the `<t>`-orbit relation. Every element of `Gamma` is `u t^k` with `u in N`, so `R_(Phi_A) = R_Gamma`.
4. **(1), the "only if" direction.** Take a `Phi_A`-path from `x` to `y = u x` with `u in N`. Its moves are `t^(+-1)`, and `s^(+-1)` applied at a point of `A` or landing in `A`, as in the partial maps `s|_A` and their inverses.
   - Write the path element as `t^(a_k) s_k^(eps_k) t^(a_(k-1)) ... s_1^(eps_1) t^(a_0)`, with total `t`-exponent `0`.
   - With partial sums `b_j = a_0 + ... + a_(j-1)`, it equals `prod_j phi^-(b_j)(s_j^(eps_j))`. The `j`-th factor is applied at an `N`-point `z_j` of the orbit.
   - The `s_j`-move happens at `t^(b_j) z_j`, so `t^(b_j) z_j in A` for `eps_j = +1`. For `eps_j = -1` the move lands in `A`: then `t^(b_j) phi^-(b_j)(s_j^-1) z_j in A`, which is the reverse of the `G_A`-edge at the endpoint for `s_j`.
   - So the path is a `G_A`-path. Hence `R_(Phi_A) ∩ R_N` is exactly the relation "connected in `G_A`". If `Phi_A` generates `R_Gamma`, then `G_A` is connected on almost every `N`-orbit.
5. **(2).** For the shift `(g x)(h) = x(g^-1 h)`, `t^m(u x) in A` iff `x(u^-1 t^-m) < delta`. The map `(u, m) -> u^-1 t^-m` is injective on `N x Z`, and `b_Gamma` has independent uniform coordinates. So the open pairs are independent with probability `delta`. In the coordinate `u` of `z = u x`, the edge `{z, phi^-m(s) z}` is `{u, phi^-m(s) u}`.
6. **(3).** Almost-sure connectivity of `T_delta` gives `C(b_Gamma) <= 1 + |S| delta` by (1) and (2). Every aperiodic relation has cost at least `1`, so letting `delta -> 0` gives `C(b_Gamma) = 1`.
7. **(4).** For `phi = id`, the edge `{u, s u}` is present iff some `(u, m)` is open, which holds almost surely since `m` ranges over `Z`.
8. **(5).** `t x_i t^-1 = x_(i+1)`, so `phi^-m(x^(+-1)) = x_(-m)^(+-1)`. The elements `x_i` freely generate `N`, so `Cay(N, {x_i^(+-1)})` is a tree, and `T_delta` is a subgraph of it.
   - The undirected edge `{u, x_(-m) u}` is present iff `(u, m)` or `(x_(-m) u, m)` is open. Its probability is `1 - (1 - delta)^2 <= 2 delta`.
   - Two tree edges can share a pair, e.g. `{u, x_(-m) u}` and `{u, x_(-m)^-1 u}` both use `(u, m)`. But edges at distance at least 3 in the tree use disjoint pairs, and there are infinitely many such edges.
   - The events "edge kept" for these edges are independent, each of probability at most `2 delta < 1`. So almost surely one of them is missing.
   - Removing any edge disconnects a tree, so `T_delta` is almost surely disconnected.
