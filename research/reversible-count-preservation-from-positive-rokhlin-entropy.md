---
rg: 2
id: reversible-count-preservation-from-positive-rokhlin-entropy
kind: route
title: A positive-entropy action gives a positive Rokhlin supremum, which a count-raising reversible automaton would force to zero
target: reversible-automata-that-never-lower-rest-counts-preserve-them
requires:
  - every-group-has-positive-rokhlin-entropy-action
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - count-raising-reversible-automata-lower-biased-rokhlin-entropy
---

Let `ψ` on `A^G` be bijective, fix `a^G`, and never lower the count of non-rest sites. Suppose it raises the count
of some finitely supported configuration.

1. By the first prerequisite, `G` has a free ergodic p.m.p. action of positive Rokhlin entropy.
2. By the second, `h^Rok_sup(G) > 0`.
3. By the reversible form of the third, `h^Rok_sup(G) = 0`.

This is a contradiction, so `ψ` preserves every count.

The argument is per group: POS(`G`) alone excludes count-raising reversible automata over `G`. The first
prerequisite is open, so this route establishes nothing yet.
