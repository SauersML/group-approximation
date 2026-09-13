---
rg: 2
id: finite-perfect-free-pairs-normal-rank-one-proof
kind: route
title: Lift an involution tuple and an odd tuple from the semisimple quotient, then apply coprime killing
target: finite-perfect-free-pairs-have-normal-rank-one
requires:
  - coprime-order-normal-generators-give-normal-rank-one
---

Let `A` be a nontrivial finite perfect group.

1. **Maximal normal subgroups.** Let `M_1, ..., M_r` (`r >= 1`) be the distinct
   maximal normal subgroups of `A`, and put `S_i = A/M_i`.
   - Each `S_i` is simple, by the correspondence theorem.
   - Each `S_i` is nonabelian: it is a nontrivial quotient of a perfect group,
     hence perfect, and an abelian perfect group is trivial.
2. **Normal generators.** An element `g` normally generates `A` exactly when it
   lies in no `M_i`.
   - If `<<g>> != A`, then `<<g>>` is a proper normal subgroup, so it lies in some
     maximal one, because `A` is finite.
   - Conversely, each `M_i` is proper and normal.
3. **Normal subgroups of `P = T_1 × ... × T_k`,** with each `T_i` nonabelian
   simple. Let `K` be normal in `P`, and let `J` be the set of `i` with
   `π_i(K) != 1`.
   - For `i ∈ J`, `π_i(K)` is a nontrivial normal subgroup of `T_i`, so it equals
     `T_i`.
   - For `k ∈ K` and `s ∈ T_i`, the commutator `[k,s]` lies in `K`, because `K` is
     normal. It lies in `T_i`, because `T_i` is normal. It equals `[π_i(k), s]`.
   - These commutators generate `[T_i,T_i] = T_i`, so `T_i ⊆ K`.
   - Hence `K = ∏_{i∈J} T_i`, and the maximal normal subgroups of `P` are the
     kernels `ker π_j`.
4. **`φ: A -> ∏_{i<=r} S_i` is onto.** Induct on `k`, with `N_k = M_1 ∩ ... ∩ M_k`.
   Assume `A/N_k ≅ ∏_{i<=k} S_i`.
   - **`N_k` is not contained in `M_{k+1}`.** If it were, `M_{k+1}/N_k` would be a
     maximal normal subgroup of `∏_{i<=k} S_i`. By step 3 it would then be some
     `M_j/N_k` with `j <= k`, contradicting distinctness.
   - **So `N_k M_{k+1} = A`,** since it is a normal subgroup strictly containing
     the maximal `M_{k+1}`.
   - **`A -> A/N_k × A/M_{k+1}` is onto.** Given `(xN_k, yM_{k+1})`, write
     `x^{-1}y = nm` with `n ∈ N_k` and `m ∈ M_{k+1}`, and put `z = xn = ym^{-1}`.
     Its kernel is `N_{k+1}`.
5. **Choosing the tuples.**
   - Each `S_i` has even order, by Feit–Thompson: groups of odd order are
     solvable, and `S_i` is not. By Cauchy it has an involution `t_i`.
   - `|S_i|` is not a power of 2, because finite 2-groups are nilpotent. So some
     odd prime `p_i` divides `|S_i|`, and there is an element `u_i` of order `p_i`.
6. **A normal generator of 2-power order.**
   - Lift `x = (t_i)` to `h ∈ A`, and write `ord(h) = 2^e m` with `m` odd.
   - `g = h^m` has order `2^e`, and `φ(g) = x^m = x` because `x^2 = 1`.
   - Every coordinate of `φ(g)` is nontrivial, so `g` lies in no `M_i`, and step 2
     says `g` normally generates `A`.
7. **A normal generator of odd order.**
   - Lift `y = (u_i)` to `k`, and write `ord(k) = 2^f n` with `n` odd.
   - `c = k^{2^f}` has odd order `n`.
   - Its coordinates `u_i^{2^f}` are nontrivial, since `p_i` is odd and does not
     divide `2^f`. So `c` normally generates `A`.
8. **Conclusion.** For nontrivial finite perfect `A` and `B`, take `a ∈ A` of
   order `2^e` and `b ∈ B` of odd order, both normal generators (steps 6 and 7).
   - `gcd(2^e, ord b) = 1`, so `coprime-order-normal-generators-give-normal-rank-one`
     gives `<<ab>> = A * B`.
   - `A * B` is nontrivial, so its normal rank is exactly 1. ∎

**Standard inputs, not re-read.**
- W. Feit and J. G. Thompson, *Solvability of groups of odd order*, Pacific J.
  Math. 13 (1963), no. 3. The theorem is the title.
- Cauchy's theorem.
- Finite p-groups are nilpotent.
