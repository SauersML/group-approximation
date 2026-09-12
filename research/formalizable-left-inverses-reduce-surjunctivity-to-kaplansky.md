---
rg: 2
id: formalizable-left-inverses-reduce-surjunctivity-to-kaplansky
kind: route
title: Formalize some left inverse of an injective binary automaton, then linearize under stable finiteness
target: stable-finiteness-forces-binary-surjunctivity
requires:
  - injective-binary-automata-have-formalizable-left-inverses
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

1. **Formalize.** Let `tau` be injective on `(F_2^n)^G`. By the first prerequisite, some left inverse
   `sigma` and some representatives satisfy `sigma o tau = id` formally.
2. **Linearize.** Stable finiteness of `F_2[G]` makes `M_n(F_2[G])` directly finite. By the second
   prerequisite, `tau o sigma = id`, so `tau` is surjective.

This route needs strictly less than `formalizable-pairs-reduce-surjunctivity-to-kaplansky`, whose
prerequisite asks formalizability for every left inverse. The older route stays valid.
