---
rg: 2
id: thompson-v-lift-into-rank-four-cohn-group-proof
kind: route
title: The boundary action on eventually-zero sequences is a finitary correction of the prefix replacement, and Whitehead's lemma moves it into EL_4
target: thompson-v-lifts-into-rank-four-cohn-elementary-group
requires:
  - cohn-elementary-group-rank-radical-is-trivial-or-everything
  - binary-leavitt-unit-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

Artifact Section 4, Propositions 4.1 and 4.2 and Corollary 4.3.

1. **Lift.** `V` permutes the eventually-zero sequences `E = {w 1 0^inf} ⊔ {0^inf}`. Transport this to
   `F_2[W] (+) F_2[W]` through `w 1 0^inf -> delta_w` in the first copy and `0^inf -> delta_empty` in
   the second, fixing every other basis vector. For a code pair `nu_i -> mu_i`, the operator agrees
   with `sum s_(mu_i) t_(nu_i) (+) 1` off finitely many basis vectors, so its entries lie in `C_2`.
   Faithfulness of the Toeplitz representation makes `phi` a homomorphism, and `pi` gives
   `diag(g, 1)`.
2. **Rank four.** `[a, b] (+) 1_2 in EL_4(C_2)`, and `V` is perfect.
3. **Rank-four dichotomy.** Run the proof of `cohn-elementary-group-rank-radical-is-trivial-or-everything`
   with four rows. The finitary kernel is simple with trivial centralizer, and the quotient
   `EL_4(R) = GL_4(R) ~ R^x` is simple.
4. **Ordering.**
   - **V gate.** It kills `phi(V)`, which meets `K_4` trivially, so the kernel is `G_4`.
   - **Cohn `EL_3`.** A nontrivial model of `G_4` yields an injective one, which restricts
     injectively to `EL_3(C_2)`.
   - **To `R^x`.** `G_4 <= EL_4(R) ~ R^x`, and nontrivial models of `R^x` are injective.
