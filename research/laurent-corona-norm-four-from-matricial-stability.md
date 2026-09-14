---
rg: 2
id: laurent-corona-norm-four-from-matricial-stability
kind: route
title: Correct corona lifts of the Laurent lattice to genuine congruence representations and read off the invariant vector
target: laurent-sl4-corona-representations-have-block-sl2-norm-four
requires: [laurent-sl4-matricially-stable, laurent-sl-n-representations-have-sl2-invariant-vectors]
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

Artifact part 1, Section 5.

1. **Lift.** Let `π : C*(Λ) → Q = ∏_n M_{k_n}/⊕_n M_{k_n}` be unital, and lift each `π(g)` to a unitary `φ_n(g)` by
   polar decomposition. This is an asymptotic homomorphism of `Λ = SL_4(F_q[t^{±1}])`.
2. **Correct.** `laurent-sl4-matricially-stable` gives homomorphisms `π_n : Λ → U(k_n)` with
   `‖φ_n(g) − π_n(g)‖ → 0` for each `g`. So `π(z) = [(π_n(z))_n]`.
3. **Read off the norm.** By `laurent-sl-n-representations-have-sl2-invariant-vectors`, each `π_n` with `k_n ≥ 1` has a
   block-`SL_2` fixed vector, so `‖π_n(z)‖ = 4`. Infinitely many `k_n ≥ 1` because `π` is unital, and the corona norm is
   the `limsup`. So `‖π(z)‖ = 4`.
