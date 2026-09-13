---
rg: 2
id: stw27-counterexample-from-hilbert-cube-indivisible-unit
kind: route
title: A Hilbert cube witness with indivisible unit is a nuclear strict-comparison algebra that is not pure
target: stw27-strict-comparison-non-pure-algebra-exists
requires: [hilbert-cube-bauer-strict-comparison-indivisible-unit-exists, bauer-strict-comparison-pure-iff-divisible-unit]
---

Let `A` witness `hilbert-cube-bauer-strict-comparison-indivisible-unit-exists`: it is
unital, simple, separable, nuclear and non-elementary, it has strict comparison, its
trace simplex is Bauer, and its unit is not tracially `N`-divisible for some `N`.

- **Stably finite.** `T(A)` is nonempty and `A` is simple, so every tracial state is
  faithful, and its amplifications are faithful on every `M_k(A)`. A faithful tracial
  state rules out infinite projections, so `A` is stably finite.
- **Not pure.** Nuclear algebras are exact, so
  `bauer-strict-comparison-pure-iff-divisible-unit` applies. There (a) ⟺ (e), and (e)
  fails, so `A` is not pure. Its Cuntz semigroup is almost unperforated by strict
  comparison, so almost divisibility is what fails.

So `A` witnesses `stw27-strict-comparison-non-pure-algebra-exists`.
