---
rg: 2
id: collapse-above-rokhlin-supremum-gives-bernoulli-collapse
kind: route
title: Exact collapse above the supremum on the binary Leavitt units, if their supremum is zero, gives isomorphic 2- and 3-shifts
target: some-group-has-isomorphic-bernoulli-shifts-of-different-entropy
requires:
  - bernoulli-shifts-above-rokhlin-supremum-are-isomorphic
  - leavitt-units-have-zero-rokhlin-entropy-supremum
---

Let `U = L_(F_2)(1,2)^x`, a countably infinite group.

1. By the second prerequisite, every free ergodic p.m.p. action of `U` has Rokhlin entropy `0`. So
   `h^Rok_sup(U) = 0 < ∞`.
2. The uniform bases on 2 and 3 points have entropies `log 2` and `log 3`, and `0 < log 2 < log 3 < ∞`.
3. The first prerequisite, applied to `G = U`, gives `2^U ≅ 3^U`.

This is Seward's specific question (arXiv:1805.08279v1, introduction) over a nonsofic group.

**Where both inputs stand.**
- The second prerequisite follows from a strict injective automaton over `U`
  (`leavitt-zero-rokhlin-supremum-from-strict-automaton`), and so from any Kaplansky or stable finiteness
  failure over a finite field.
- The first prerequisite is an Ornstein-type theorem with no known mechanism
  (its Attempts section).
