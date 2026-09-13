---
rg: 2
id: nonsofic-free-burnside-gives-nonsofic-hyperbolic-group-proof
kind: route
title: Converge the Delzant--Gromov stages to B(m,N) in the space of marked groups and apply closedness
target: nonsofic-free-burnside-gives-nonsofic-hyperbolic-group
requires:
  - free-burnside-is-a-limit-of-hyperbolic-groups
  - local-approximation-properties-are-marked-closed
---

**Setup.**
- Fix `m >= 2` and an odd `N >= n_1(F_m)`.
- Let `F_m = G_0 -> G_1 -> ...` be the sequence of
  `free-burnside-is-a-limit-of-hyperbolic-groups`. Mark each `G_k`, and
  `B(m,N)`, by the images of a fixed free basis of `F_m`.
- Write `N_k = ker(F_m -> G_k)` and `N_inf = F_m^N`.
- Let `P` be a property `P_M` of `local-approximation-properties-are-marked-closed`,
  for instance soficity or hyperlinearity.

1. **The kernels increase to `F_m^N`.**
   - Each `G_k -> G_{k+1}` is a surjection, so `N_k <= N_{k+1}`.
   - By item 3 of the literature claim, the union of the `N_k` is `N_inf`. In
     particular every `N_k <= N_inf`.
2. **The balls stabilize.** Fix `R`, and let `S_{2R}` be the finite set of
   reduced words of length `<= 2R` in `F_m`.
   - Each of the finitely many elements of `S_{2R} ∩ N_inf` lies in some `N_k`.
   - Since the `N_k` increase, there is `k(R)` such that
     `S_{2R} ∩ N_k = S_{2R} ∩ N_inf` for all `k >= k(R)`.
   - For such `k`, take words `u, v` of length `<= R`. Then `u = v` in `G_k`
     iff `u^{-1}v ∈ N_k`, iff `u^{-1}v ∈ N_inf`, iff `u = v` in `B(m,N)`.
   - So `G_k` and `B(m,N)` satisfy the same equalities among words of length
     `<= R`. The same holds for the relations `w = 1` with `|w| <= R`.
3. **Closedness.** Suppose `B(m,N)` fails `P`.
   - Clause 3 of `local-approximation-properties-are-marked-closed` gives a
     radius `R`. Every `m`-generated marked group whose words of length `<= R`
     satisfy the same equalities as in `B(m,N)` fails `P`.
   - By step 2, `G_k` fails `P` for every `k >= k(R)`.
4. **Hyperbolicity.** By item 1 of the literature claim, each `G_k` is a
   non-elementary hyperbolic group.

The contrapositive is the positive form: if `P` holds for infinitely many
`G_k`, it holds for `B(m,N)`.

**Remark.** The same argument applies to `G/G^N` for any non-elementary
torsion-free hyperbolic `G` and odd `N >= n_1(G)`. The claim states only the
free case.
