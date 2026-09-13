---
rg: 2
id: sl3z-incoherent-via-euler-fibered-subgroup
kind: route
title: A two-dimensional fibred subgroup with nonzero Euler characteristic makes SL_3(Z) incoherent
target: sl3z-is-incoherent
requires:
  - sl3z-contains-cd2-euler-positive-fibered-subgroup
---

Let `G <= SL_3(Z)` be of type FP with `cd G = 2`, `chi(G) != 0`, and let
`phi: G -> Z` be onto with finitely generated kernel `N`. Suppose `N` were
finitely presented. We derive a contradiction.

1. `N` is of type FP. Take a partial resolution `P_2 -> P_1 -> P_0 -> Z -> 0`
   by finitely generated free `ZN`-modules, which exists because `N` is
   finitely presented. The kernel `K` of `P_1 -> P_0` is a quotient of `P_2`,
   so it is finitely generated. It is projective by dimension shifting, since
   `cd N <= cd G = 2`. So `0 -> K -> P_1 -> P_0 -> Z -> 0` is a finite
   projective resolution. In particular `H_k(N; Q)` is finite dimensional for
   every `k` and zero for `k > 2`.
2. Wang sequence. For the extension `G = N x| <t>` there is an exact sequence
   `... -> H_k(N;Q) --(t_* - 1)--> H_k(N;Q) -> H_k(G;Q) -> H_{k-1}(N;Q) --(t_* - 1)--> H_{k-1}(N;Q) -> ...`.
   Write `c_k` and `z_k` for the dimensions of the cokernel and kernel of
   `t_* - 1` on `H_k(N; Q)`. Exactness gives `dim H_k(G; Q) = c_k + z_{k-1}`.
   An endomorphism of a finite-dimensional space has kernel and cokernel of
   equal dimension, so `z_j = c_j`.
3. So `chi(G) = sum_k (-1)^k (c_k + c_{k-1}) = 0`. This contradicts
   `chi(G) != 0`.

Hence `N` is finitely generated and not finitely presented, and `SL_3(Z)` is
incoherent. This is the classical Euler-characteristic mechanism, in the form
used for free-by-free groups. The argument above is self-contained and does
not rely on Bieri's normal-subgroup theorem.
