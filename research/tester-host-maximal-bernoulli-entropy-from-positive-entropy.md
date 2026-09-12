---
rg: 2
id: tester-host-maximal-bernoulli-entropy-from-positive-entropy
kind: route
title: One positive-entropy free ergodic action of the tester host gives maximal Bernoulli Rokhlin entropy on it
target: bernoulli-rokhlin-entropy-maximal-on-fixed-tester
requires:
  - tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy
  - tester-host-has-positive-rokhlin-entropy-action
---

The first prerequisite is established: POS(`U`) implies RBS(`U`), in particular `h^Rok_U(A^U, uniform) = log |A|` for every finite alphabet. The second prerequisite is open. So this is a valid implication with an open hypothesis.

It forms a deliberate cycle with `tester-host-positive-entropy-from-maximal-bernoulli-entropy`. Both implications are true, the two claims are equivalent, and the least fixpoint establishes neither.
