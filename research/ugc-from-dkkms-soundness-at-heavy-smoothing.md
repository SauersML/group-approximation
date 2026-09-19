---
rg: 2
id: ugc-from-dkkms-soundness-at-heavy-smoothing
kind: route
title: Run the folded DKKMS reduction at a fixed smoothing rate, lift it to a unique game with the quotient free bit, and take k large enough that the class seed spread is below eta
target: unique-games-conjecture
requires: [dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games, dkkms-2to1-game-sound-at-heavy-smoothing]
artifacts:
  - experiments/ugc-free-bit-2026-09-17/quotient_seed_posterior.py
---

Fix `eps > 0`. We show that `Gap-UG[1 - eps, eps]` is NP-hard.

## The parameters

1. Apply `dkkms-2to1-game-sound-at-heavy-smoothing` with `delta = eps`. This
   gives `l >= 3`, `beta in (0,1)`, `s in (1/2, 1)` and `k_1`.
2. Using Theorem H of `dkkms-quotient-free-bit-lifts-seed-mass-to-unique-games`,
   pick `k >= k_1` with `xi(l,k,beta) <= eps/2`. This is possible because
   `xi -> 0` at fixed `(l, beta)`.
3. Put `eps_3 := min(eps/(2k), s - 1/2)`. By Håstad, `Gap3Lin[1 - eps_3, 1/2 + eps_3]`
   is NP-hard on regular instances. Since `1/2 + eps_3 <= s`,
   the NO side has value `<= s`.

## The reduction

The map is `I -> Lift(G(I; l,k,beta))`, the quotient free-bit lift. For fixed
`(l,k)` it has polynomial size, alphabet `2^l`, and is computed in polynomial
time by Theorem F(1).

## The two cases

- **YES.** An assignment of value `>= 1 - eps_3` satisfies all `k` equations of
  a tuple with probability `>= 1 - k eps_3`. Tuple equations are marginally
  uniform on a regular instance, so the union bound applies and
  `eps_out <= eps/2`. By Theorem F(3), `val >= 1 - xi - eps_out >= 1 - eps`.
- **NO.** Here `val(I) <= s`. By Theorem F(2) and the hole,
  `val(Lift) <= val(G) <= eps`.

This is `unique-games-conjecture` with alphabet `2^l`.

## Independence of the prerequisites

The two prerequisites can fail independently.

- The free-bit node is ESTABLISHED. It fails only if its proof is wrong.
- The hole is a soundness statement about the NO side only, at a parameter
  point that no recorded result covers.
