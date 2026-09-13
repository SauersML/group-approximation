---
rg: 2
id: sl4z-corona-block-sl2-norm-four-from-matricial-stability
kind: route
title: Correct corona lifts to genuine representations and read off the Magee-de la Salle fixed vector
target: sl4z-corona-representations-have-block-sl2-norm-four
requires: [sl4z-matricially-stable, sl4z-representations-have-sl2-invariant-vectors]
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13.md
---

Artifact, Section 4, Theorem 3.

1. **Lift.**  Let `pi : C*(SL_4(Z)) -> Q_k` be unital, and lift each `pi(g)` to a
   unitary `phi_n(g)`.  This is an asymptotic homomorphism.
2. **Correct.**  `sl4z-matricially-stable` gives homomorphisms `rho_n : SL_4(Z) -> U(k_n)`
   with `||phi_n(g) - rho_n(g)|| -> 0` for each `g`.  So
   `pi(S + S^-1 + T + T^-1) = [(rho_n(S + S^-1 + T + T^-1))_n]`.
3. **Read off the norm.**  By `sl4z-representations-have-sl2-invariant-vectors`, each
   `rho_n` with `k_n >= 1` has a block-`SL_2(Z)` fixed vector.  So its Laplacian has norm
   `4`.  Infinitely many `k_n` are `>= 1` because `pi` is unital, and the corona norm is
   the `limsup`.  So `||pi(S + S^-1 + T + T^-1)|| = 4`.
