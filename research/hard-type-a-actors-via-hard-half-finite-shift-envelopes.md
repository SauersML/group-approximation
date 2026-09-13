---
rg: 2
id: hard-type-a-actors-via-hard-half-finite-shift-envelopes
kind: route
title: A finitely presented half-finite shift envelope with hard generators is a hard type (A) actor
target: type-a-actors-with-arbitrarily-hard-word-problem
requires: [hard-half-finite-permutations-have-fp-shift-envelopes, half-finite-shift-envelope-wp-computes-generators, half-finite-generators-with-e2-are-strongly-shift-similar, fp-strongly-shift-similar-admits-type-a-action]
---

Fix a recursive `T` and put `T+(m) = m + max_(k<=m) T(k)`, which is recursive
and non-decreasing. Put `R(n) = (n+3)^2 T+((n+3)^2)`.

1. **Hard generators with a finitely presented envelope.** By
   `hard-half-finite-permutations-have-fp-shift-envelopes`, applied to `R`, there
   are half-finite `gamma_1, ..., gamma_k` with `gamma_i(x) <= 4x`. Some
   evaluation map `n -> gamma_i(n)` lies outside `F(R)`, and
   `G = <gamma_1, ..., gamma_k, sl, flip, (1 2)>` is finitely presented.
2. **A type (A) action.** By Observation 1 of
   `half-finite-generators-with-e2-are-strongly-shift-similar`,
   `G = <gamma_1, ..., gamma_k, E_2>`, so by its Proposition 2, `G` is strongly
   shift-similar. Being finitely presented, `G` admits an action of type (A), by
   `fp-strongly-shift-similar-admits-type-a-action` (Zaremsky, Proposition 5.3).
3. **Hardness.** By the consequence clause of
   `half-finite-shift-envelope-wp-computes-generators` with `K = 4`, the word
   problem of `G` lies outside `F(T+)` for every finite generating set. Since
   `T <= T+`, also `F(T) <= F(T+)`, so it lies outside `F(T)`.

So for every recursive `T` there is a faithful type (A) action of a finitely
presented group whose word problem beats `T`. `∎`
