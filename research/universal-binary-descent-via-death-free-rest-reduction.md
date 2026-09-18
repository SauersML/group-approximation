---
rg: 2
id: universal-binary-descent-via-death-free-rest-reduction
kind: route
title: Merge rest symbols without letting any active site die, fix the parity by a binary identity factor, then carry phases on free fiber orbits
target: some-nonsurjunctive-group-gives-a-binary-one
requires:
  - strict-automata-reduce-to-few-rest-self-relaying-ones
  - self-relaying-donor-covering-automata-reach-admissible-types
  - donor-covering-strict-automata-descend-to-two-symbols
---

Compared with `universal-binary-descent-via-rest-symbol-reduction`: that route needs a reduction landing in type
`(2, b)` with `4 ∤ b`. This one needs a reduction landing in any self-relaying type with at most two rest symbols, and
supplies the 2-adic condition itself.

Assume `NS_all ≠ ∅`. By `strict-automata-reduce-to-few-rest-self-relaying-ones`, some group `G` carries a strict
self-relaying donor-covering automaton of type `(z, b)` with `z ∈ {1, 2}`. By
`self-relaying-donor-covering-automata-reach-admissible-types`, `G` carries a strict donor-covering automaton of type
`(1, b')` with `b'` odd or `(2, b')` with `4 ∤ b'`. By item 4 of `donor-covering-strict-automata-descend-to-two-symbols`,
`2 ∈ NS_all`.

**What this route uses from the third prerequisite.** Only item 4, together with items 1-3 that it rests on. The audit
of 2026-09-17 found those items sound and returned the node to OPEN only because its title claims every type with at
most two rest symbols. The corrected statement, with the 2-adic conditions in place, is all that is used here.

**What it isolates.** The first prerequisite is equivalent to the target, given items 3 and 4, so this route is a
reformulation. It removes the 2-adic bookkeeping and the open node
`donor-covering-few-rest-automata-reach-admissible-types` from the universal problem. What remains is one geometric
requirement: reduce the number of rest symbols while no active input site ever becomes rest.
