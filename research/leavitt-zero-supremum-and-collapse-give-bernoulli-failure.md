---
rg: 2
id: leavitt-zero-supremum-and-collapse-give-bernoulli-failure
kind: route
title: Zero Rokhlin supremum on the binary Leavitt unit group plus collapse at zero supremum gives isomorphic Bernoulli shifts of different entropy
target: some-group-has-isomorphic-bernoulli-shifts-of-different-entropy
requires:
  - leavitt-units-have-zero-rokhlin-entropy-supremum
  - zero-rokhlin-supremum-forces-bernoulli-collapse
---

Let `U = L_(F_2)(1,2)^x`, a countably infinite group. By the first prerequisite, every
free ergodic p.m.p. action of `U` has Rokhlin entropy `0`, so `h^Rok_sup(U) = 0`. The
second prerequisite then gives finite bases of different Shannon entropy whose Bernoulli
shifts over `U` are isomorphic. So `U` witnesses the target.

**Scope.** By part (d) of `bernoulli-entropy-counterexample-constraints`, every countable
group containing `U` also witnesses the target. The first prerequisite follows from a
strict automaton over `U` (`leavitt-zero-rokhlin-supremum-from-strict-automaton`).
