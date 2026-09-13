---
rg: 2
id: finite-simple-groups-converge-to-simple-kazhdan-group-proof
kind: route
title: Primitive return words make the periodic models full matrix algebras, so the elementary images generate SL_3N(F_q) and converge to S
target: finite-simple-groups-converge-to-simple-kazhdan-group
requires: [simple-kazhdan-lef-group-from-minimal-subshift, minimal-subshift-algebra-is-simple-lef-ring, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/simple-kazhdan-lef-consequences-and-sources-2026-09-12.md
---

Artifact Part 2, §8.1.

1. **Primitive models.** Replace the periodic word `w_k` of the ring models by its primitive root
   `z_k`. The bi-infinite periodic sequence is unchanged, so every cyclic window of length `<= 2k+1`
   lies in `L(X)`, and every word of `L_(2k+1)(X)` occurs. A primitive cyclic word of length `N` has
   at most `N` distinct windows of a given length, while `|L_(2k+1)(X)| >= 2k+2` for an aperiodic
   subshift. So `N_k = |z_k| >= 2k+2 -> infinity`.
2. **Full matrix algebras.** Products of shifted letter indicators `P^i D(chi_[a]) P^(-i)` give the
   diagonal indicator of every cyclic window. The word `z_k` is primitive, so two positions with the
   same cyclic windows of length `N_k` are equal. Thus these diagonals generate all diagonal matrices,
   and together with `P` they generate `M_(N_k)(F_q)`. The images of the elementary generators
   therefore generate `EL_3(M_(N_k)(F_q)) = SL_(3N_k)(F_q)`.
3. **Convergence to `G`.** The maps `psi_k` are injective and multiplicative on the ball of radius
   `r` once `k` is large. So a word of length `<= r` is trivial in `G` iff it is trivial in
   `SL_(3N_k)(F_q)` for large `k`. That is marked convergence.
4. **Convergence to `S`.** Suppose `psi_k(g) psi_k(g')^(-1) = λ I` with `g, g'` in the ball. Then
   `psi_k(g^(-1) g') = psi_k(λ I_3)`, so `g^(-1) g' = λ I_3 ∈ G` and `λ ∈ Λ`. So quotienting by the
   full centre of `SL_(3N_k)(F_q)` changes no ball relations beyond `Z(G) = Λ I_3`, and
   `PSL_(3N_k)(F_q) -> S` in marked-group space. `S` is simple by the first prerequisite.
5. **Expanders.** All the marked approximants are quotients of `EL_3(F_q<t_1, ..., t_m>)`, with `m`
   the number of ring generators, which is Kazhdan by the third prerequisite. So they are uniform
   expanders.
