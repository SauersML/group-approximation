---
rg: 2
id: weakly-sofic-surjunctivity-via-hamming-transport
kind: route
title: Transport weakly sofic models to finite actions and run the Gromov--Weiss count
target: weakly-sofic-groups-are-surjunctive
requires:
  - weak-sofic-models-admit-uniform-hamming-transports
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
---

**Dead.** It is invalidated by
`hamming-transports-of-weak-sofic-models-are-soficity`, and its prerequisite is
refuted.

The idea: from weakly sofic models, produce finite actions with small Hamming
defects and fixed separation for every finite set. Then run the Gromov--Weiss
count, which is the proof of `sofic-groups-are-surjunctive`.

Why it dies:
- Such actions are sofic approximations, so the prerequisite holds only for
  sofic groups.
- For those groups `sofic-groups-are-surjunctive` already applies.
- Every nonsofic weakly sofic group, the Kun--Thom wreath for one, defeats the
  prerequisite.
- Fibre absorption at a normal subgroup `N` of the model is the special case
  `V = H/N`. It needs exact local embeddings into `H/N`.

What is not killed: a count that uses transports only on the finite set of a
single strict automaton. See artifact Section 3 for why that escape is narrow.
