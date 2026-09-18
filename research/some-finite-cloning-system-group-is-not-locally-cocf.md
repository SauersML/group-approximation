---
rg: 2
id: some-finite-cloning-system-group-is-not-locally-cocf
kind: claim
title: "Some cloning system on finite groups has a Thompson-like group that is not locally coCF"
artifacts:
  - research/artifacts/zp-lehnert-2-16-2026-09-13.md
  - experiments/cloning-period-growth-2026-09-17/phi_and_counter_circuit.py
  - experiments/cloning-period-growth-2026-09-17/output.txt
---

There is a cloning system on finite groups `G_n` whose Thompson-like group
`T(G_*)` (or some finitely generated subgroup of it) is not co-context-free.
This is the negative answer to the coCF sub-question of Zaremsky Problem 2.16;
if established it is the negation of
`finite-cloning-system-groups-are-locally-cocf`.

## Attempts

- Route via period growth: a f.g. group with period growth `≻ exp(n^4)` is not
  coCF (Bishop–Bodart–Issini–Perego, arXiv:2601.13058, Thm 2.7). Build a
  compatible cloning system on finite `G_n` whose exponents grow (so that words
  of length `n` reach elements of order `≻ exp(n^4)`), analogous to how the
  Brin–Thompson group `2V` has non-recursive period growth. Difficulty: the
  cloning axioms (C1)–(C3) tie `G_{n+1}` to `G_n` through `ρ_n`, and the natural
  finite families used so far (symmetric, signed-symmetric, direct powers,
  upper-triangular over a finite ring) have bounded exponent or exponent growing
  only polynomially in `n`, which the `V`-tree geometry damps to `⪯ exp(n^2)`.
  No such family is known to this lane; this is the open direction.
- Closed (2026-09-17, swarm-0917-w4-pull-z-1): the period-growth route above works, with a family whose exponent grows
  doubly exponentially.
  - Family: `G_n = Sym({0,1}^n)`, pure, where `κ^n_k` inserts a fixed bit at coordinate `k+1`.
  - Short words reach large orders because `F` places 3-bit gates on any three of the first `w` bits at cost `O(w)`.
  - A product of `O(s^2)` placed gates runs a reversible counter with a controlled swap. It has word length
    `≤ 248 s^3` and order `≥ lcm(1..2^s−1) ≥ 2^(2^s−2)/3`.
  - By BBIP's explicit bound `n·ord(g) ≤ 2^((mn^2+1)^2)`, the subgroup `Γ` is not coCF.
  - Nodes: `bit-register-cloning-group-has-doubly-exponential-period-growth` and
    `cocf-group-torsion-order-bounded-by-word-length`, combined in route
    `finite-cloning-group-not-locally-cocf-by-period-growth`.
  - Numerical checks: `experiments/cloning-period-growth-2026-09-17/`.
  - The "polynomial exponent damped to `exp(n^2)`" heuristic above fails for `Sym({0,1}^n)`. Cloning doubles the number
    of states of a register without doubling any leaf count.
