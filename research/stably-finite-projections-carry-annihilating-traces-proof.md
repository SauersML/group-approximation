---
rg: 2
id: stably-finite-projections-carry-annihilating-traces-proof
kind: route
title: Take the six-term kernel over the projection-generated ideal, apply Lemma A on its unital corner, and extend by infinity
target: stably-finite-projections-carry-annihilating-traces
requires: [moutzouris-singular-subgroup-has-vanishing-trace]
artifacts:
  - research/artifacts/bk-af-killing-projection-traces-2026-09-13.md
---

Proposition B in §2 of the artifact.

1. By six-term exactness, `ι_P^{-1}(H)` is the kernel of `K_0(I_P) -> K_0(E)`.
2. A projection `e ∈ M_k(I_P)` with `[e] = 0` in `K_0(E)` satisfies
   `e ⊕ 1_m ~ 1_m`, so `e = 0` by stable finiteness.  So the kernel is singular.
3. `K_0(P M_n(I_P) P) ≅ K_0(I_P)` as ordered groups.  Lemma A (the Q-stability-free
   form of Moutzouris Lemma 2.12 with Haagerup and Blackadar–Rørdam, recorded in
   `moutzouris-singular-subgroup-has-vanishing-trace`) gives a tracial state `t`
   vanishing on the singular subgroup.
4. Extend `t` to a densely finite trace on `M_n(I_P)` and by `+∞` off it.
