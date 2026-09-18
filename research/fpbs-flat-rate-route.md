---
rg: 2
id: fpbs-flat-rate-route
kind: route
title: A flat walk rate at one supercritical parameter forbids uniqueness there by Harris-FKG
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-flat-walk-rate-past-pc-universal
  - fpbs-sublinear-zero-interpolant-iff-flat-rate
artifacts:
  - research/artifacts/fpbs-sublinear-zero-flat-rate-2026-09-18.md
---

Hole [F] gives `p_+ > p_c` with `a_n(p_+) <= rho^n`. Apply the uniqueness
consequence of `fpbs-sublinear-zero-interpolant-iff-flat-rate`. Monotonicity
gives `a_n(p) <= rho^n -> 0` for every `p <= p_+`. If there were a unique
infinite cluster at such `p`, Harris-FKG would give `a_n(p) >= theta(p)^2`.
So `p_u >= p_+ > p_c`.

**Why this decomposition.**

- [F] is the common weakest point of the two complex-analytic and Fourier
  routes. Both [A] (`fpbs-flat-rate-from-fourier-algebra`) and ZG
  (`fpbs-flat-rate-from-zero-free-polynomials`) imply it.
- The equivalence theorem shows that no interpolant-type zero-free hypothesis
  is weaker than [F]. A zero-free route therefore closes BS only through [F].
- [F] is a single real inequality at one parameter. It is failable on its own:
  a Cayley graph with `lambda(p) > rho` for every `p > p_c` refutes it without
  refuting BS. Trees show that `lambda > rho` is compatible with nonuniqueness.
