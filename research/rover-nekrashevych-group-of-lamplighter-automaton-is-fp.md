---
rg: 2
id: rover-nekrashevych-group-of-lamplighter-automaton-is-fp
kind: claim
title: The Rover-Nekrashevych group of the lamplighter automaton is finitely presented, although Z/2 wr Z is neither finitely presented nor contracting
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that imports sufficient conditions (G finitely presented, or G contracting); this is an example satisfying neither.
  rover-nekrashevych-fp-iff-finite-lift-presentation: that is the general characterization; this applies it to one non-contracting, infinitely presented group.
---

**ESTABLISHED (proof in `rover-nekrashevych-group-of-lamplighter-automaton-is-fp-proof`; unreviewed).**

## Statement

Let `a = σ(a, b)` and `b = (a, b)` over `X = {0, 1}`, where `σ` is the transposition. This is the Grigorchuk–Żuk
lamplighter automaton, and `G = ⟨a, b⟩ ≅ Z/2 ≀ Z`.

**Theorem B.**

1. `G` is not contracting, and not finitely presented.
2. Its relator kernel is `N = K_∞`: every relator of `G` becomes freely trivial after finitely many splittings.
3. Hence `V_2(G)` is finitely presented. A presentation consists of the Higman–Thompson relations of `V_2`, together
   with Nekrashevych's commutation relations (C) and splitting relations (S) for `S = {a, b}^{±1}`. No further
   relator is needed.

Neither sufficient condition in `rover-nekrashevych-finite-presentation-criteria` covers `G`: Scott's needs `G`
finitely presented, and Nekrashevych's needs `G` contracting. As far as the sources read go, this is the first
non-contracting self-similar group whose Rover–Nekrashevych group is known to be finitely presented.

## Attempts

- 2026-09-18 (w7-101): proved via `rover-nekrashevych-fp-iff-finite-lift-presentation` (Theorem A, the
  `N = K_∞` case). Put `c = b^{-1}a = σ(c, c^{-1})` and `d_k = b^k c b^{-k}`.
  - `c^2` dies after one splitting.
  - `[c, d_k]` splits into squares of products of `d_j` with `|j| < k`, so it lies in `K_∞` by induction on `k`.
  - Thus `F/K_∞` is a quotient of `Z/2 ≀ Z`. Hopficity then gives `N = K_∞`.
  - Machine check: `experiments/nonc-rn-fp-2026-09-17/lamp.py` confirms `[c, d_k] in K_∞` for `k <= 10`.
  - Next: F_∞ for `V_2(G)`, and other bounded or linear-activity automata. `scan.py` lists their short relators
    outside `K_∞`.
