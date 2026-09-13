---
rg: 2
id: brin-thompson-2v-nonsurjunctive-from-averaging-fullness
kind: route
title: A full averaging idempotent in the binary group algebra of 2V gives a strict automaton over 2V
target: brin-thompson-2v-nonsurjunctive
requires:
  - brin-thompson-2v-order-three-averaging-idempotent-is-full
  - stable-finiteness-failure-refutes-surjunctivity
---

Given `c e b = 1`, put `a = e b` and `d = c`, so `d a = 1`. If also `a d = 1`, then `e = e (e b c) = e b c = 1`.
That is false, because `g ⊗ 1 != 1` in `2V`. So `F_2[2V]` is not directly finite, and
`stable-finiteness-failure-refutes-surjunctivity` gives an injective non-surjective automaton over `2V`
(`research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md`, Proposition 2.1).
