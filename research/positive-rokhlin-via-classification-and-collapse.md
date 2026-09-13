---
rg: 2
id: positive-rokhlin-via-classification-and-collapse
kind: route
title: Base-entropy classification for every group plus collapse at zero supremum gives positive Rokhlin entropy for every group
target: every-group-has-positive-rokhlin-entropy-action
requires:
  - bernoulli-shift-entropy-classifies-for-every-group
  - zero-rokhlin-supremum-forces-bernoulli-collapse
---

Fix a countably infinite group `G`, and suppose no free ergodic p.m.p. action of `G`
has positive Rokhlin entropy.
- Then every free ergodic action with finite Rokhlin entropy has Rokhlin entropy `0`,
  so `h^Rok_sup(G) = 0` by the definition of the supremum.
- The second prerequisite gives finite bases of different Shannon entropy whose
  Bernoulli shifts over `G` are isomorphic.
- That contradicts the first prerequisite for `G`.

So every countably infinite group has a free ergodic action of positive Rokhlin
entropy.

**Scope.**
- The converse route `bernoulli-classification-via-positive-rokhlin-entropy` derives
  the first prerequisite from the target. Once the second prerequisite is established,
  the two roots are equivalent.
- The argument works group by group: INV(G) together with the second prerequisite for
  `G` gives POS(G).
- The intended cycle with the converse route is recorded here.
