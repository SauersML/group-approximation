---
rg: 2
id: universal-binary-descent-via-rest-symbol-reduction
kind: route
title: Reduce a strict automaton to two rest symbols with relays for its active sites, then carry the phases on free fiber orbits
target: some-nonsurjunctive-group-gives-a-binary-one
requires:
  - strict-automata-reduce-to-two-rest-donor-covering-ones
  - donor-covering-strict-automata-descend-to-two-symbols
---

Assume some group is not surjunctive over some finite alphabet, so `NS_all ≠ ∅`. By
`strict-automata-reduce-to-two-rest-donor-covering-ones`, some group `G` carries a strict donor-covering automaton of
type `(2, b)` with `4 ∤ b`. By item 4 of `donor-covering-strict-automata-descend-to-two-symbols`, `2 ∈ NS(G × C_p)`
for some prime `p`. So some group is not surjunctive over two symbols.

The two prerequisites are of different kinds. The second is established and purely algebraic. The first is equivalent
to the target (item 5 of the second), so this route is a reformulation. What it isolates is that the only quantity
to reduce is the number of rest symbols.
