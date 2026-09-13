---
rg: 2
id: houghton-groups-have-quadratic-dehn-function
kind: claim
title: "For every n >= 3, Houghton's group H_n has quadratic Dehn function"
distinct_from:
  houghton-groups-have-polynomial-dehn-function: that asks only for some polynomial bound; this asks for the sharp bound x^2, which with the quadratic lower bound pins the Dehn function exactly.
---

For every `n >= 3` and every finite presentation of Houghton's group `H_n`,
the Dehn function satisfies `δ_(H_n)(x) ≃ x^2`.

The lower bound `x^2 ≼ δ` is established
(`houghton-groups-have-at-least-quadratic-dehn-function`), so this claim is
equivalent to the upper bound `δ ≼ x^2`.

## Attempts

- 2026-09-13 (z1-24-houghton): the plan is a normal form
  `σ · g_1^(m_1) ... g_(n-1)^(m_(n-1))`, with `σ` a sorted product of canonical
  transposition words, and a combing estimate. Sorting the translation letters
  costs `O(x^2)` relator applications but creates `O(x^2)` conjugates of `α`.
  The whole cost then sits in the areas of the commutation and conjugation
  relations among transpositions at distance `<= x` from the origin. A
  quadratic bound needs those areas to be linear on average, which requires
  cheap transporters: translations along lines that avoid a given finite set
  and commute with a given transposition through relators of bounded area.
  Not yet established.
