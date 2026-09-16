---
rg: 2
id: binary-surjunctivity-split-by-memory-size
kind: route
title: Split by memory size; at most three elements is support-three direct finiteness over F_2
target: every-group-is-binary-surjunctive
requires:
  - binary-three-address-strict-automata-are-linear
  - f2-support-three-one-sided-units-are-units
  - binary-four-plus-memory-automata-are-surjunctive
---

Let `G` be a group and `tau : {0,1}^G -> {0,1}^G` an injective cellular automaton. We show that
`tau` is surjective.

- **No memory with at most three elements.** Then `tau` is surjective by
  `binary-four-plus-memory-automata-are-surjunctive`.
- **Some memory with at most three elements.** Suppose `tau` is not surjective.
  - By `binary-three-address-strict-automata-are-linear`, a minimal memory `M = {m_0, m_1, m_2}`
    has three elements.
  - Its rule is `x_0 + x_1 + x_2 + epsilon`.
  - With `a = m_1 m_0^-1` and `b = m_2 m_0^-1`, the element `1 + a + b in F_2[G]` has a left inverse
    but is not a unit.
  - Here `1, a, b` are distinct, so `1 + a + b` has support three.
  - That contradicts `f2-support-three-one-sided-units-are-units`. So `tau` is surjective.

The two cases are exhaustive, so every group is surjunctive for the two-symbol full shift.

The three-element half is an equivalence: by the same claim, a support-three one-sided unit over
`F_2` that is not a unit gives a strict binary automaton with three memory elements.
