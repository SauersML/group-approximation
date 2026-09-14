---
rg: 2
id: laurent-linear-confining-sets-infinite-order-proof
kind: route
title: A generic conjugate of diag(u,1,u^{-1}) makes the trace of [p, k^m] non-constant for all large |m|, and pigeonhole puts one such commutator into H
target: laurent-linear-confining-sets-force-infinite-order-elements
requires:
  - confined-subgroup-pigeonhole-commutator-lemma
---

**Proof.** Let `A = F_2[u^{±1}]`, `d = diag(u,1,u^{-1})`, `K = \overline{F_2(u)}`.
1. **The invariant.** For `h ∈ SL_3(K)` put `Φ_p(h) = (h^{-1}ph)_{31}(h^{-1}p^{-1}h)_{13}`, a regular function on `SL_3`.
   - If `p ≠ 1`, then `p` is not scalar (the only scalar in `SL_3(F_2(u))` is 1). Take `v` with `pv ∉ F_2(u)v` and `h = (v | λw | pv)` with `det h = 1`.
   - Then `h^{-1}ph·e_1 = e_3` and `h^{-1}p^{-1}h·e_3 = e_1`, so `Φ_p(h) = 1`.
2. **A generic `h`.** The union of the zero sets of `Φ_p`, `p ∈ P`, is proper in the irreducible `SL_3`. `Λ` is Zariski dense, since it contains the root groups `e_ij(F_2[u])` with `F_2[u]` infinite. So fix `h ∈ Λ` with `Φ_p(h) ≠ 0` for all `p ∈ P`, and put `k = hdh^{-1}`.
3. **The trace.** With `p′ = h^{-1}ph`, `q′ = h^{-1}p^{-1}h ∈ SL_3(A)` and entries of degree `≤ D`:
   - `tr[p,k^m] = tr[p′,d^m] = Σ_{i,l} p′_{il}q′_{li}u^{m(d_l−d_i)}` with `(d_1,d_2,d_3) = (1,0,−1)`;
   - for `|m| > 4D` the classes `d_l − d_i = δ` occupy disjoint degree ranges, and the class `δ = 2` equals `Φ_p(h)u^{2m} ≠ 0`. So the trace is not constant.
4. **Infinite order.** A finite-order element of `SL_3(A)` has root-of-unity eigenvalues, so its trace is algebraic over `F_2`, hence lies in `F_2`. So `[p,k^m]` has infinite order for every `p ∈ P` and `|m| > 4D`.
5. **Pigeonhole.** Put `g_i = k^{N_i}` for `N_1 < … < N_{r+1}` with gaps `> 4D`. `confined-subgroup-pigeonhole-commutator-lemma` gives `g_i^{-1}[p,k^{N_i−N_j}]g_i ∈ H`, of infinite order. ∎

Model tests and the necessity of the twist `h` (`[e_12(1),d^m] = e_12(1+u^m)` has order 2): artifact §3.
