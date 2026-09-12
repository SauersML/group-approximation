---
rg: 2
id: every-pair-formalizable-gives-formalizable-left-inverses
kind: route
title: An injective binary automaton has a left inverse by compactness, and formalizing that pair gives a formalizable left inverse
target: injective-binary-automata-have-formalizable-left-inverses
requires:
  - binary-left-inverse-pairs-are-formalizable
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Let `tau` be injective on `(F_2^n)^G`.
- **Left inverse.** By compactness, some finite window of `tau(x)` determines `x(1)`. Extending that
  local rule arbitrarily to all patterns gives an automaton `sigma` with `sigma o tau = id`.
- **Formalize.** The prerequisite makes the pair `(tau, sigma)` formalizable.
